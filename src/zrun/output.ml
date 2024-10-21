(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  (c) 2020-2024 Inria Paris                                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

open Format
open Lident
open Value
   
let lident ff lid =
  match lid with
  | Name(s) -> fprintf ff "%s" s
  | Modname { qual; id } -> fprintf ff "%s.%s" qual id
                          
let rec print_list value ff l =
  match l with
  | [] -> assert false
  | [x] -> value ff x
  | x :: l -> printf "@[%a,@ %a@]" value x (print_list value) l
            
let rec pvalue ff v =
  match v with
  | Vint(i) -> fprintf ff "%i" i
  | Vbool(b) -> fprintf ff "%s" (if b then "true" else "false")
  | Vfloat(f) -> fprintf ff "%f" f
  | Vchar(c) -> fprintf ff "%c" c
  | Vstring(s) -> fprintf ff "%s" s
  | Vvoid -> fprintf ff "()"
  | Vtuple(l) ->
     fprintf ff "@[<hov 1>(%a)@]" value_list l
  | Vstuple(l) ->
     fprintf ff "@[<hov 1>(%a)@]" pvalue_list l
  | Vconstr0(lid) -> lident ff lid
  | Vconstr1(lid, l) ->
     fprintf ff "@[<hov1>%a(%a)@]" lident lid pvalue_list l 
  | Vstate0(id) -> Ident.fprint_t ff id
  | Vstate1(id, l) ->
     fprintf
       ff "@[<hov 1>%a(%a)@]" Ident.fprint_t id pvalue_list l
  | Vfun _ ->
     fprintf ff "<fun>"
  | Vclosure { c_funexp = { f_kind } } ->
     fprintf ff "<%s>" (Printer.kind f_kind)
  | Vsizefun _ ->
     fprintf ff "<sizefun>"
  | Vsizefix { bound; name; defs } ->
     let n_list = Ident.Env.to_list defs in
     fprintf ff "<sizefix <%a>%a with %a>"
       (Pp_tools.print_opt
          (fun ff i_list -> 
             Pp_tools.print_list_l (fun ff i -> fprintf ff "%d" i)
               "(" "," "" ff i_list)) bound Ident.fprint_t name
       (Pp_tools.print_list_r 
          (fun ff (name, _) -> Ident.fprint_t ff name) "" "," "") n_list
  | Vrecord(l) ->
     let one ff { Zelus.arg; Zelus.label } =
       fprintf ff "@[<hov2>%a =@ %a@]"
         pvalue arg Lident.fprint_t label in
     (Pp_tools.print_list_r one "{" ";" "}") ff l
  | Vabsent ->
     fprintf ff "abs"
  | Vpresent(v) ->
     fprintf ff "!%a" pvalue v
  | Varray(a) -> parray ff a

and parray ff a =
  match a with
  | Vflat(v) ->
     fprintf ff "@[<hov1>[|%a|]@]"
       (fun ff v ->
         Array.iter (fun x -> fprintf ff "%a;@," pvalue x) v)
       v
  | Vmap(m) -> pmap ff m

and pmap ff { m_length; m_u } = fprintf ff "@[[%d] -> ...@]" m_length

and value ff v =
  match v with
  | Vnil -> fprintf ff "nil"
  | Vbot -> fprintf ff "bot"
  | Value(v) -> pvalue ff v                 
              
and pvalue_list ff l = print_list pvalue ff l
                     
and value_list ff l = print_list value ff l
                    

(* print a state *)
let rec pstate ff s =
  match s with
  | Sbot -> fprintf ff "bot"
  | Snil -> fprintf ff "nil"
  | Sempty -> fprintf ff "()"
  | Sval(v) -> value ff v
  | Sstatic(v) -> fprintf ff "@[(static %a)@]" pvalue v
  | Slist(s_list) ->
      (Pp_tools.print_list_l pstate "[" ";" "]") ff s_list
  | Sopt(None) -> 
     fprintf ff "none" | Sopt(Some(v)) -> fprintf ff "(some %a)" value v
  | Sinstance { init } ->
     fprintf ff "@[<hov2>(instance@ %a)@]" pstate init
  | Scstate { pos; der } -> 
     fprintf ff "@[{ pos = %a; der = %a }@]" value pos value der
  | Szstate { zin; zout } ->
     fprintf ff "@[{ zin = %b; zout = %a }@]" zin value zout
  | Shorizon { zin; horizon } -> 
     fprintf ff "@[{ zin = %b; zout = %f }@]" zin horizon
  | Speriod { phase; period } -> 
     fprintf ff "@[{ phase = %f; period = %f }@]" phase period
  | Senv _ -> fprintf ff "@[(env)@]"

let pstate ff s =
  fprintf ff "%a@." pstate s

let value_flush ff v =
  fprintf ff "%a@." value v
let pvalue_flush ff l = 
  fprintf ff "%a@." pvalue l
let letdecl ff n_v_list =
  let onedecl ff (name, v) =
    fprintf ff "@[<hov 2>val %s =@ %a@]@." name pvalue v in
  List.iter (onedecl ff) n_v_list
