(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2015                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)
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
   
(* the main node must be of type [expected_ty_arg] and the result of *)
(* type [expected_ty_res] *)
let check_type_of_main_node name 
			    { qualid = qualid; info = { value_typ = tys } } 
			    expected_ty_arg expected_ty_res =
  try
    let k, _, ty_args, ty_res = Types.instance_of_type_signature tys in
    (* check input and output types *)
    begin match ty_args with
     | [ty_arg] -> 
        Types.unify ty_arg expected_ty_arg;
        Types.unify ty_res expected_ty_res;
     | _ -> raise Types.Unify
    end;
    qualid, k
  with
    | Types.Unify ->
        eprintf "The input and output types of %s should be %a and %a.@." 
          name Ptypes.output expected_ty_arg Ptypes.output expected_ty_res;
      raise Misc.Error

(* the  main node must be of type [unit -> unit] in case of sampled simulation *)
let check_unit_unit name info =
  check_type_of_main_node name info Initial.typ_unit Initial.typ_unit

(* the  main node must be of type [unit -> bool] in case of bounded testing *)
let check_unit_bool name info =
  check_type_of_main_node name info Initial.typ_unit Initial.typ_bool

let emit_prelude ff ({ Lident.id = id } as qualid) k =
  (* the prelude *)
  let s = Lident.qualidname qualid in
  match k with
  | Deftypes.Tany | Deftypes.Tdiscrete(false) ->
      fprintf ff
        "@[(* simulation (any) function *)
           let main () = %s();;@.@]" s

  | Deftypes.Tdiscrete(true) ->
      fprintf ff
        "@[(* simulation (discrete) function *)\n\
           let main = let mem = %s_alloc () in fun _ -> %s_step mem ();;@.@]" s s  

  | Deftypes.Tcont ->
      (* first generate the top-level machine *)
      let m = Inout.simulate (Lident.Modname qualid) in
      (* emit the code *)
      Modules.initialize (String.capitalize_ascii id);
      Oprinter.machine_as_functions ff "main" m

(* emited code for control-driven programs: the transition function *)
(* is executed at full speed *)
let emit_simulation_code ff k =
  match k with
  | Deftypes.Tany | Deftypes.Tdiscrete _ ->
      fprintf ff
          "@[(* (discrete) simulation loop *)\n\
             while true do main () done;\n\
             exit(0);;@.@]"
  | Deftypes.Tcont ->
      fprintf ff "@[(* instantiate a numeric solver *)\n\
                    module Runtime = Zlsrun.Make (Defaultsolver)\n\
                    let _ = Runtime.go main@.@]"

(* emited code for bounded checking. Check that the function returns [true] *)
(* during [n] steps *)
let emit_checked_code ff k n =
  match k with
  | Deftypes.Tany | Deftypes.Tdiscrete _ ->
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
      
let emit_gtkmain_code ff k sampling =
  match k with
  | Deftypes.Tany | Deftypes.Tdiscrete _ ->
      fprintf ff
        "@[(* simulation loop: sampled on period %f Hz *)\n@.@]" sampling;
      fprintf ff "@[(* instantiate the discrete interface *)\n\
                    module Runtime = Zlsrungtk.MakeDiscrete ()\n\
                    let _ = Runtime.go %f main@.@]" sampling
  | Deftypes.Tcont ->
      fprintf ff "@[(* instantiate a numeric solver *)\n\
                    module Runtime = Zlsrungtk.Make (Defaultsolver)\n\
                    let _ = Runtime.go main@.@]"

(* emited code for event-driven programs: the transition function *)
(* is executed every [1/sampling] seconds *)
let emit_periodic_code ff k sampling =
  match k with
  | Deftypes.Tany | Deftypes.Tdiscrete _ ->
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

(** The main entry function. Simulation of a main function *)
let main name sampling number_of_checks use_gtk =
  (* - open the module where main occurs
     - makes a module of that name
     - instanciate main inside it
     - compile it *)
  let filename = name ^ ".ml" in
  let info = find name in
  let qualid, k =
    if number_of_checks > 0 then check_unit_bool name info 
    else check_unit_unit name info in
  let oc = open_out filename in
  let ff = Format.formatter_of_out_channel oc in
  emit_prelude ff qualid k;
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
    else if use_gtk then emit_gtkmain_code ff k sampling
    else
      if sampling = 0.0 then emit_simulation_code ff k
      else emit_periodic_code ff k sampling;
  close_out oc

