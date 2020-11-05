(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2020 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* glue code for simulating a main node *)

open Deftypes
open Global
open Format
open Misc

(*
   Generating a main .ml file in order to simulate a node.

   - in sampling mode, the simulated node should be of type
     [unit -> unit]
   - otherwise, generates an instantiated transition function *)

(* check if [name] is defined *)
let find name =
  try
    Modules.find_value (Lident.Name(name))
  with
  | Not_found ->
      eprintf "The name %s is unbound.@." name;
      raise Misc.Error

(* the main node must be of type [expected_ty_arg_list] and the result of *)
(* type [expected_ty_res_list] *)
let check_type_of_main_node name
    { qualid = qualid; info = { value_typ = tys } }
    opt_name expected_ty_arg expected_ty_res =
  let actual_ty = Types.instance_of_type tys in
  let actual_k, opt_name, actual_ty_arg, actual_ty_res =
    try
      Types.filter_actual_arrow actual_ty
    with
    | _ ->  eprintf "@[The name %s must define a function.@.@]" name;
        raise Misc.Error in
  let expected_k =
    match actual_k with | Tproba -> Tdiscrete(true) | _ -> actual_k in
  let expected_ty =
    Types.funtype expected_k opt_name actual_ty_arg actual_ty_res in
  try
    Types.unify expected_ty actual_ty; qualid, expected_k
  with
  | Types.Unify ->
      eprintf "@[The name %s has type@ %a,@ \
               but is expected to have type@ %a.@.@]"
        name
        Ptypes.output actual_ty
        Ptypes.output expected_ty;
      raise Misc.Error

(* the  main node must be of type [unit -> unit] *)
(* in case of sampled simulation *)
let check_unit_unit name info =
  check_type_of_main_node name info None Initial.typ_unit Initial.typ_unit

(* the  main node must be of type [unit -> bool] in case of bounded testing *)
let check_unit_bool name info =
  check_type_of_main_node name info None Initial.typ_unit Initial.typ_bool

let rec is_unit ty =
  match ty.t_desc with
  | Tlink ty -> is_unit ty
  | Tconstr (id, _, _) -> id.id = "unit"
  | _ -> false

let allowed_types = Initial.(Lident.(List.map (fun qualid -> qualid.id)
                                       [int_ident; bool_ident; float_ident; unit_ident]))
let unit_id = Initial.unit_ident.Lident.id

let rec check_simple_ty ty =
  match ty.t_desc with
  | Tvar ->
      eprintf "Undefined type variables are not supported by Luciole.@.";
      raise Misc.Error
  | Tfun _ ->
      eprintf "Higher order functions are not supported by Luciole.@.";
      raise Misc.Error
  | Tvec _ ->
      eprintf "Vectors are not supported by Luciole.@.";
      raise Misc.Error
  | Tproduct ty -> List.iter check_simple_ty ty
  | Tconstr (id, _, _) ->
      if List.mem id.id allowed_types then () else begin
        eprintf "Type %s is not allowed.@." id.id;
        raise Misc.Error
      end
  | Tlink ty -> check_simple_ty ty

let rec flatten ty =
  match ty.t_desc with
  | Tproduct ty -> List.concat (List.map flatten ty)
  | Tconstr (id, _, _) -> [id.id]
  | Tlink ty -> flatten ty
  | Tvar | Tfun _ | Tvec _ -> assert false

let rec flatten_patt patt =
  match patt.Zelus.p_desc with
  | Etuplepat p_l -> List.concat (List.map flatten_patt p_l)
  | Ealiaspat (p, id) -> flatten_patt p
  | Evarpat id -> [id.source]
  | Etypeconstraintpat (p, _) -> flatten_patt p
  | Econstpat Evoid -> ["unit"]
  | Econstr0pat _ | Econstr1pat _ | Ewildpat | Econstpat _ | Eorpat _
  | Erecordpat _  -> assert false

let print_string_of_ty ff ty =
  Format.fprintf ff "string_of_%s" ty

let print_ty_of_string ff ty =
  Format.fprintf ff "%s_of_string" ty

let rec type_size ty =
  match ty.t_desc with
  | Tproduct ty ->
      List.fold_left ( + ) 0 (List.map type_size ty)
  | Tconstr (_, _, _) -> 1
  | Tlink ty -> type_size ty
  | Tvec _ | Tfun _ | Tvar -> assert false

let format_names names ty =
  let rec aux i0 ty =
    match ty.t_desc with
    | Tproduct ty -> Printf.sprintf "(%s)" (aux_list i0 ty)
    | Tconstr (id, _, _) ->
        if id.id = unit_id then "()" else names.(i0)
    | Tlink ty -> aux i0 ty
    | Tvar | Tfun _ | Tvec _ -> assert false
  and aux_list i0 ty_list =
    match ty_list with
    | [] -> assert false
    | ty :: q ->
        let names1 = aux i0 ty in
        let ofst1 = type_size ty in
        let (_, names) =
          List.fold_left (fun (ofst, names) ty ->
              let names = Printf.sprintf "%s, %s" names (aux (i0 + ofst) ty) in
              let ofst = ofst + (type_size ty) in
              (ofst, names)) (ofst1, names1) q
        in names
  in aux 0 ty

let emit_open ff open_list =
  List.iter (fprintf ff "@[%s@]@.") open_list

let emit_discrete_main k ff name =
  match k with
  | Deftypes.Tstatic _ | Deftypes.Tany | Deftypes.Tdiscrete(false) ->
      fprintf ff
        "@[<v>@[(* simulation (any) function *)@]@;\
         @[let main x = %s x@]@]" name
  | Deftypes.Tdiscrete(true) ->
      fprintf ff
        "@[<v>@[(* simulation (discrete) function *)@]@;\
         @[<v 2>@[let main =@]@;\
         @[let open Ztypes in@]@;\
         @[let %s { alloc = alloc; step = step; reset = reset } = %s in@]@;\
         @[let mem = alloc () in@]@;\
         @[reset mem;@]@;\
         @[(fun x -> step mem x)@]@]@]"
        (if !Misc.with_copy then "Cnode" else "Node") name
  | Deftypes.Tcont | Deftypes.Tproba -> assert false

let emit_prelude ff ({ Lident.id = id } as qualid) info k =
  (* the prelude *)
  let s = Lident.qualidname qualid in
  match k with
  | Deftypes.Tstatic _ | Deftypes.Tany | Deftypes.Tdiscrete(false)
  | Deftypes.Tdiscrete(true) ->
      if !use_rif then begin
        let ({ typ_vars; typ_body } as scheme) = info.info.value_typ in
        let t1, t2, inp_patt =
          begin match typ_body.t_desc with
            | Tfun (_, _, t1, t2) ->
                begin match info.info.value_code.value_exp with
                  | Global.Vfun (fexp, _) ->
                      let inp_patt = List.hd fexp.f_args in
                      t1, t2, inp_patt
                  | _ -> assert false
                end
            | _ -> assert false
          end
        in
        check_simple_ty t1;
        check_simple_ty t2;

        let flat_t1 = flatten t1 in
        let flat_t2 = flatten t2 in

        let inp_names =
          List.map2 (fun name ty -> if ty = unit_id then "_" else name)
            (flatten_patt inp_patt) flat_t1 in
        let out_names = List.mapi (fun i ty -> if ty = unit_id then "_" else "o" ^ (string_of_int i)) flat_t2 in

        let filtered_inp_names =
          List.filter_map (fun n -> if n = "_" then None else Some n) inp_names
        in
        let filtered_out_names =
          List.filter_map (fun n -> if n = "_" then None else Some n) out_names
        in

        let formatted_inp_names = format_names (Array.of_list inp_names) t1 in
        let formatted_out_names = format_names (Array.of_list out_names) t2 in

        let inp_pragma =
          Printf.sprintf "#inputs %s"
            (String.concat " "
               (List.map2 (fun id ty_id ->
                    if ty_id <> unit_id then
                      Printf.sprintf "\\\"%s\\\":%s" id ty_id
                    else "")
                   inp_names flat_t1))
        in
        let out_pragma =
          Printf.sprintf "#outputs %s"
            (String.concat ""
               (List.map2 (fun id ty_id ->
                    if ty_id <> unit_id then
                      Printf.sprintf "\\\"%s\\\":%s " id ty_id
                    else "")
                   out_names flat_t2))
        in
        fprintf ff
          "@[<v 2>@[let main =@]@;\
           @[<hov>%a@;@[in@]@]@;\
           @;\
           @[<hov 2>@[let bool_of_string s =@]@;@[s = \"T\" || s = \"t\"@]@;@[in@]@]@;\
           @;\
           @[<hov 2>@[let string_of_bool b =@]@;@[if b then \"T\" else \"F\"@]@;@[in@]@]@;\
           @;\
           @[<hov>@[let header =@]@;\
           @[<v 1>@[\"# File produced by Luciole_zls\\n\\@]@;\
           @[# Node: %s\\n\\@]@;\
           @[%s\\n\\@]@;\
           @[%s\"@]@]@,\
           @[in@]@]@;\
           @;\
           @[let step_no = ref 1 in@]@;\
           @;\
           @[Printf.printf \"%%s\\n\" header; flush stdout;@]@;\
           @[<v 3>@[(fun () ->@]@;\
           @[<hov 2>Printf.printf \"#step %%d\\n\" !step_no; flush stdout;@]@;\
           @[<hov 2>let inputs = input_line stdin in@]@;\
           %a\
           %a\
           @[<hov 2>let %s = main %s in@]@;\
           %a\
           @[<hov 2>Printf.printf \"%s\\n\" %s; flush stdout;@]@;\
           @[<hov 2>step_no := !step_no + 1@])@]@;\
           @];;@]@."
          (emit_discrete_main k) s
          s inp_pragma out_pragma
          (fun ff _ ->
             if List.length filtered_inp_names = 0 then () else
               fprintf ff "@[<hov 2>let [%s] = String.split_on_char ' ' (String.trim inputs) in@]@;"
                 (String.concat "; " filtered_inp_names)) ()
          (fun ff (inps, tys) ->
             List.iter2
               (fun inp ty ->
                  if ty <> unit_id then
                    Format.fprintf ff "@[<hov 2>let %s = %a %s in@]@;"
                      inp print_ty_of_string ty inp)
               inps tys) (inp_names, flat_t1)
          formatted_out_names formatted_inp_names
          (fun ff (inps, tys) ->
             List.iter2
               (fun inp ty ->
                  if ty <> unit_id then
                    Format.fprintf ff "@[<hov 2>let %s = %a %s in@]@;"
                      inp print_string_of_ty ty inp)
               inps tys) (out_names, flat_t2)
          (String.concat " " (List.map (fun _ -> "%s") filtered_out_names))
          (String.concat " " (List.filter_map (fun n -> if n = "_" then None else Some n) out_names));
      end else
        fprintf ff "@[%a;;@]@." (emit_discrete_main k) s
  | Deftypes.Tcont ->
      if !use_rif then begin
        eprintf "Cannot use option -rif with hybrid main node.@.";
        raise Misc.Error
      end else
      fprintf ff
        "@[<v>@[open Ztypes@]@;\
         @[open Zls@]@;\
         @;\
         @[(* simulation (continuous) function *)@.\
         @[<hov2>let main = @,\
         @[<v>\
         @[<hov2>let cstate = @,\
         @[<hov2>{ dvec = cmake 0; cvec = cmake 0; @,\
         zinvec = zmake 0; zoutvec = cmake 0; @,\
         cindex = 0; zindex = 0; @,\
         cend = 0; zend = 0; @,\
         cmax = 0; zmax = 0; @,\
         major = false; horizon = 0.0 }@] in@] @,\
         @[<hov2>let %s \
         { alloc = alloc; step = hstep; reset = reset } = \
         %s cstate in@] @,\
         @[<hov2>let step mem cvec dvec zin t = @,\
         @[cstate.major <- true; @,\
         cstate.cvec <- cvec; @,\
         cstate.dvec <- dvec; @,\
         cstate.cindex <- 0; @,\
         cstate.zindex <- 0; @,\
         cstate.horizon <- infinity;  @,\
         hstep mem (t, ()) in@]@]@,\
         @[<hov2>let derivative mem cvec dvec zin zout t = @,\
         @[cstate.major <- false;  @,\
         cstate.cvec <- cvec; @,\
         cstate.dvec <- dvec; @,\
         cstate.zinvec <- zin; @,\
         cstate.zoutvec <- zout; @,\
         cstate.cindex <- 0; @,\
         cstate.zindex <- 0; @,\
         ignore (hstep mem (t, ())) in@]@]@,\
         @[<hov2>let crossings mem cvec zin zout t = @ \
         @[cstate.major <- false;  @,\
         cstate.cvec <- cvec; @,\
         cstate.zinvec <- zin; @,\
         cstate.zoutvec <- zout; @,\
         cstate.cindex <- 0; @,\
         cstate.zindex <- 0; @,\
         ignore (hstep mem (t, ())) in@]@]@,\
         @[<hov2>let maxsize mem = cstate.cmax, cstate.zmax in@]@,\
         @[<hov2>let csize mem = cstate.cend in@]@,\
         @[<hov2>let zsize mem = cstate.zend in@]@,\
         @[<hov2>let horizon mem = cstate.horizon in@]@,\
         @[<hov1>Hsim @[<hov2>{ alloc;@ step;@ reset;@ derivative; @,\
         crossings; @,\
         maxsize; @ csize; @ zsize; @,\
         horizon }@]@]@];;@]@.@]@]"
        (if !Misc.with_copy then "Cnode" else "Node") s
  | Tproba -> assert false

(* emited code for control-driven programs: the transition function *)
(* is executed at full speed *)
let emit_simulation_code ff k =
  match k with
  | Deftypes.Tstatic _ | Deftypes.Tany | Deftypes.Tdiscrete _ ->
      fprintf ff
        "@[(* (discrete) simulation loop *)\n\
         while true do main () done;\n\
         exit(0);;@.@]"
  | Deftypes.Tcont ->
      fprintf ff "@[(* instantiate a numeric solver *)\n\
                  module Runtime = Zlsrun.Make (Defaultsolver)\n\
                  let _ = Runtime.go main@.@]"
  | Deftypes.Tproba -> assert false

(* emited code for bounded checking. Check that the function returns [true] *)
(* during [n] steps *)
let emit_checked_code ff k n =
  match k with
  | Deftypes.Tstatic _ | Deftypes.Tany | Deftypes.Tdiscrete _ ->
      fprintf ff
        "@[(* (discrete) simulation loop *)
           let ok = ref true in
           for i = 0 to %d - 1 do
             let r = main () in
             if not r then begin
                 print_string (\"error(\" ^ (string_of_int i) ^ \")\\n\");
                 exit(2)
               end
             else ok := r
           done;
           exit(0)@.@]" n

  | Deftypes.Tcont ->
      fprintf ff "@[(* instantiate a numeric solver *)\n\
                  module Runtime = Zlsrun.Make (Defaultsolver)\n\
                  let _ = Runtime.check main %d@.@]" n
  | Deftypes.Tproba -> assert false

let emit_gtkmain_code ff k sampling =
  match k with
  | Deftypes.Tstatic _ | Deftypes.Tany | Deftypes.Tdiscrete _ ->
      fprintf ff
        "@[(* simulation loop: sampled on period %f Hz *)\n@.@]" sampling;
      fprintf ff "@[(* instantiate the discrete interface *)\n\
                  module Runtime = Zlsrungtk.MakeDiscrete ()\n\
                  let _ = Runtime.go %f main@.@]" sampling
  | Deftypes.Tcont ->
      fprintf ff "@[(* instantiate a numeric solver *)\n\
                  module Runtime = Zlsrungtk.Make (Defaultsolver)\n\
                  let _ = Runtime.go main@.@]"
  | Deftypes.Tproba -> assert false

(* emited code for event-driven programs: the transition function *)
(* is executed every [1/sampling] seconds *)
let emit_periodic_code ff k sampling =
  match k with
  | Deftypes.Tstatic _ | Deftypes.Tany
  | Deftypes.Tdiscrete _ ->
      fprintf ff
        "@[(* simulation loop: sampled on period %f *)\n\
         (* compiles with -custom unix.cma    *)@.@]" sampling;
      fprintf ff
        "@[let periodic() =
              let _x = Unix.setitimer Unix.ITIMER_REAL
              {Unix.it_interval = %f ; Unix.it_value = 1.0 }
              in Sys.set_signal Sys.sigalrm (Sys.Signal_handle main);
              while true do Unix.sleep 1 done;;
              periodic();exit(0)@.@]" sampling
  | Deftypes.Tcont ->
      fprintf ff "@[(* instantiate a numeric solver *)
                 let _ = Zlsrun.go main@.@]"
  | Deftypes.Tproba -> assert false

(** The main entry function. Simulation of a main function *)
let main outname name sampling number_of_checks use_gtk =
  (* - open the module where main occurs
     - makes a module of that name
     - instanciate main inside it
     - compile it *)
  let outname = match outname with None -> name | Some s -> s in
  let filename = outname ^ ".ml" in
  let info = find name in
  let qualid, k =
    if number_of_checks > 0 then check_unit_bool name info
    else check_unit_unit name info in
  let oc = open_out filename in
  let ff = Format.formatter_of_out_channel oc in
  emit_prelude ff qualid info k;
  if number_of_checks > 0 then
    if sampling <> 0.0 then
      begin
        eprintf "Do not use -sampling when checking node %s.@." name;
        raise Misc.Error
      end
    else
      emit_checked_code ff k number_of_checks
  else
  if sampling < 0.0 then
    eprintf "Do not use -sampling with a negative argument.@."
  else if use_gtk then emit_gtkmain_code ff k 1.
  else
  if sampling = 0.0 then emit_simulation_code ff k
  else emit_periodic_code ff k sampling;
  close_out oc
