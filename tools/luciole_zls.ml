
open Misc
open Deftypes
open Initial
open Compiler

let compile file =
  if Filename.check_suffix file ".zls" || Filename.check_suffix file ".zlus"
  then
    let filename = Filename.chop_extension file in
    let modname = String.capitalize_ascii (Filename.basename filename) in
    compile modname filename
  else if Filename.check_suffix file ".zli"
  then
    let filename = Filename.chop_suffix file ".zli" in
    let modname = String.capitalize_ascii (Filename.basename filename) in
    interface modname filename
  else if Filename.check_suffix file ".mli"
  then
    let filename = Filename.chop_suffix file ".mli" in
    let modname = String.capitalize_ascii (Filename.basename filename) in
    scalar_interface modname filename
  else
    raise (Arg.Bad ("don't know what to do with " ^ file))

let doc_verbose = "\t Set verbose mode"
let doc_vverbose = "\t Set even more verbose mode"
and doc_version = "\t The version of the compiler"
and doc_outname = "<name> \t Simulation file name <name>"
and doc_print_types = "\t Print types"
and doc_print_causality_types = "\t Print causality types"
and doc_print_initialization_types = "\t  Print initialization types"
and doc_include = "<dir> \t Add <dir> to the list of include directories"
and doc_stdlib = "<dir> \t Directory for the standard library"
and doc_locate_stdlib = "\t  Locate standard libray"
and doc_no_stdlib = "\t  Do not load the stdlib module"
and doc_typeonly = "\t  Stop after typing"
and doc_hybrid = "\t  Select hybrid translation"
and doc_simulation =
  "<node> \t Simulates the node <node> and generates a file <out>.ml\n\
   \t\t   where <out> is equal to the argument of -o if the flag\n\
   \t\t   has been set, or <node> otherwise\n\
   \t\t   For hybrid programs, compile with:\n\
   \t\t   bigarray.cma unix.cma -I +sundials sundials_cvode.cma \n\
   \t\t   zllib.cma"
and doc_sampling = "<p> \t Sets the sampling period to p (float <= 1.0)"
and doc_check = "<n> \t Check that the simulated node returns true for n steps"
and doc_use_gtk =
  "\t Use lablgtk2 interface.\n\
   \t\t   Compile with: -I +lablgtk2 lablgtk.cma \n\
   \t\t   zllibgtk.cma"
and doc_inlining_level = "<n> \t Level of inlining"
and doc_inline_all = "\t Inline all function calls"
and doc_dzero = "\t Turn on discrete zero-crossing detection"
and doc_nocausality = "\t (undocumented)"
and doc_no_opt = "\t (undocumented)"
and doc_no_deadcode = "\t (undocumented)"
and doc_noinitialisation = "\t (undocumented)"
and doc_nosimplify = "\t (undocumented)"
and doc_noreduce = "\t (undocumented)"
and doc_lmm = "<n>\t Translate the node into Lustre--"
and doc_red_name = "\t Static reduction for"
and doc_zsign = "\t Use the sign function for the zero-crossing argument"
and doc_with_copy = "\t Add of a copy method for the state"
let errmsg = "Options are:"

let set_verbose () =
  verbose := true;
  Printexc.record_backtrace true

let set_vverbose () =
  vverbose := true;
  set_verbose ()

let rec is_unit ty =
  match ty.t_desc with
  | Tlink ty -> is_unit ty
  | Tconstr (id, _, _) -> id.id = "unit"
  | _ -> false

let allowed_types = List.map (fun qualid -> qualid.Lident.id)
    [Initial.int_ident; Initial.bool_ident;
     Initial.float_ident; Initial.unit_ident]
let unit_id = Initial.unit_ident.Lident.id

let rec check_ty ty =
  match ty.t_desc with
  | Tvar ->
    Format.eprintf "Undefined type variables are not supported by Luciole.\n";
    exit 2
  | Tfun _ ->
    Format.eprintf "Higher order functions are not supported by Luciole.\n";
    exit 2
  | Tvec _ ->
    Format.eprintf "Vectors are not supported by Luciole.\n";
    exit 2
  | Tproduct ty -> List.iter check_ty ty
  | Tconstr (id, _, _) ->
    if List.mem id.id allowed_types then () else begin
      Format.eprintf "Type %s is not allowed.\n" id.id;
      exit 2
    end
  | Tlink ty -> check_ty ty

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
  | Ewildpat | Econstpat _  | Econstr1pat _  | Eorpat _
  | Erecordpat _ -> assert false

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

let write_ml zls_file sim_node kind t1 t2 inp_patt =
  let basename = Filename.chop_extension (Filename.basename zls_file) in
  let module_name = String.capitalize_ascii basename in

  let out_name = Printf.sprintf "luciole_%s_%s.ml" basename sim_node in
  let out_path = Filename.concat (Filename.dirname zls_file) out_name in

  check_ty t1;
  check_ty t2;

  let flat_t1 = flatten t1 in
  let flat_t2 = flatten t2 in

  let inp_names =
    List.map2 (fun name ty -> if ty = unit_id then "_" else name)
      (flatten_patt inp_patt) flat_t1 in
  let out_names = List.mapi (fun i ty -> if ty = unit_id then "_" else "o" ^ (string_of_int i)) flat_t2 in

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

  let header = [
    "# File produced by Luciole_zls\\n\\";
    Printf.sprintf "# File: %s.zls\\n\\" basename;
    Printf.sprintf "# Node: %s\\n\\" sim_node;
    Printf.sprintf "%s\\n\\" inp_pragma;
    Printf.sprintf "%s" out_pragma
  ] in

  let out_fd = open_out out_path in
  let out_ff = Format.formatter_of_out_channel out_fd in

  Format.fprintf out_ff "@[@[let bool_of_string s =@]@;\
                         @[s = \"T\" || s = \"t\"@]@]";
  Format.fprintf out_ff "@.@.";
  Format.fprintf out_ff "@[@[let string_of_bool b =@]@;\
                         @[if b then \"T\" else \"F\"@]@]";
  Format.fprintf out_ff "@.@.";
  Format.fprintf out_ff
    "@[<h>@[<h>let header =@]@;@[<h>\"@,@[<v>%a@]@,\"@]@]"
    (fun ff l -> if l = [] then () else begin
         Format.fprintf ff "@[<h>%s@]" (List.hd l);
         List.iter (fun l -> Format.fprintf ff "@;@[<h>%s@]" l) (List.tl l)
       end) header;
  Format.fprintf out_ff "@.@.";
  begin match kind with
    | Tdiscrete true ->
      Format.fprintf out_ff
        "@[<v 2>\
         @[let mk_step (Ztypes.%s { alloc; step; reset }) =@]@;\
         @[let mem = alloc () in@]@;\
         @[reset mem;@]@;\
         @[(fun x -> step mem x)@]@]"
        (if !Misc.with_copy then "Cnode" else "Node");
    | Tdiscrete false | Tany -> Format.fprintf out_ff "@[let mk_step step = step@]";
    | _ ->
      Format.eprintf "Kind of node %s is not valid.\n"
        sim_node;
      exit 2;
  end;
  Format.fprintf out_ff "@.@.";
  Format.fprintf out_ff
    "@[<v 2>@[let _ =@]@;\
     @[let model_step = mk_step %s.%s in@]@;\
     @;\
     @[<v 2>@[let rec run n =@]@;\
     @[<hov 2>Printf.printf \"#step %%d\\n\" n; flush stdout;@]@;\
     @[<hov 2>let inputs = input_line stdin in@]@;\
     @[<hov 2>let [%s] = String.split_on_char ' ' (String.trim inputs) in@]@;\
     %a@[<hov 2>let %s = model_step %s in@]@;\
     %a@[<hov 2>Printf.printf \"%s\\n\" %s; flush stdout;@]@;\
     @[<hov 2>run (n+1)@]@]@;\
     @[in@]@;\
     @[Printf.printf \"%%s\\n\" header; flush stdout;@]@;\
     @[run 1@]@]@]"
    module_name sim_node
    (String.concat "; "
       (List.filter_map (fun n -> if n = "_" then None else Some n) inp_names))
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
    (String.concat " "
       (List.map (fun _ -> "%s")
          (List.filter_map (fun n -> if n = "_" then None else Some n) out_names)))
    (String.concat " " (List.filter_map (fun n -> if n = "_" then None else Some n) out_names));
  Format.fprintf out_ff "@.";

  close_out out_fd;

  Format.printf "@.Saved file %s.@." out_path

let main () =
  Printf.printf "----- Luciole_zls\n\n";

  let sim_node = ref "main" in
  let zls_file = ref "" in

  (* compile file *)
  begin try
      Arg.parse (Arg.align
                   [
                     "-v", Arg.Unit set_verbose, doc_verbose;
                     "-vv", Arg.Unit set_vverbose, doc_vverbose;
                     "-version", Arg.Unit show_version, doc_version;
                     "-o", Arg.String set_outname, doc_outname;
                     "-I", Arg.String add_include, doc_include;
                     "-i", Arg.Set print_types, doc_print_types;
                     "-ic", Arg.Set print_causality_types, doc_print_causality_types;
                     "-ii", Arg.Set print_initialization_types, doc_print_initialization_types;
                     "-where", Arg.Unit locate_stdlib, doc_locate_stdlib;
                     "-stdlib", Arg.String set_stdlib, doc_stdlib;
                     "-nostdlib", Arg.Unit set_no_stdlib, doc_no_stdlib;
                     "-typeonly", Arg.Set typeonly, doc_typeonly;
                     "-s", Arg.Set_string sim_node, doc_simulation;
                     "-sampling", Arg.Float set_sampling_period, doc_sampling;
                     "-check", Arg.Int set_check, doc_check;
                     "-gtk2", Arg.Set use_gtk, doc_use_gtk;
                     "-dzero", Arg.Set dzero, doc_dzero;
                     "-nocausality", Arg.Set no_causality, doc_nocausality;
                     "-nopt", Arg.Set no_opt, doc_no_opt;
                     "-nodeadcode", Arg.Set no_deadcode, doc_no_deadcode;
                     "-noinit", Arg.Set no_initialisation, doc_noinitialisation;
                     "-inline", Arg.Int set_inlining_level, doc_inlining_level;
                     "-inlineall", Arg.Set inline_all, doc_inline_all;
                     "-nosimplify", Arg.Set no_simplify_causality_type, doc_nosimplify;
                     "-noreduce", Arg.Set no_reduce, doc_noreduce;
                     "-zsign", Arg.Set zsign, doc_zsign;
                     "-copy", Arg.Set with_copy, doc_with_copy;
                     "-lmm", Arg.String set_lmm_nodes, doc_lmm
                   ])
        (fun s -> zls_file := s; compile s)
        errmsg;
    with
    | Misc.Error -> exit 2
  end;

  if !zls_file = "" then begin
    Format.eprintf "No model has been specified\n";
    exit 2
  end;

  (* get node type *)
  let res =
    try
      Modules.find_value (Name !sim_node)
    with
    | Not_found ->
      Format.eprintf "Could not find node %s\n" !sim_node;
      exit 2
  in
  let ({ typ_vars; typ_body } as scheme) = res.info.value_typ in

  Format.printf "Found value %s of type %a@."
    !sim_node Ptypes.print_scheme scheme;

  begin match typ_body.t_desc with
    | Tfun (k, _, t1, t2) ->
      let Global.Vfun (fexp, _) = res.info.value_code.value_exp in
      let inp_patt = List.hd fexp.f_args in
      write_ml !zls_file !sim_node k t1 t2 inp_patt
    | _ ->
      Format.eprintf "Type %a of value %s is not valid.\n"
        Ptypes.print_scheme scheme !sim_node;
      exit 2;
  end

let _ = main ()
