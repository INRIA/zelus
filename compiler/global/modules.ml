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

(* global symbol tables *)
open Misc
open Lident
open Deftypes
open Global

module E = Map.Make (struct type t = string let compare = compare end)
  
exception Already_defined of string

exception Cannot_find_file of string
  
type env =
    { mutable name: string;
      mutable values: Global.value_desc E.t;
      mutable types: Global.type_desc E.t;
      mutable constr: Global.constr_desc E.t;
      mutable label: Global.label_desc E.t;
    }
      
type modules =
    { current: env;              (* associated symbol table *)
      mutable opened: env list;  (* opened tables *)
      mutable modules: env E.t;  (* tables loaded in memory *)
    }
      
let current = 
  { name = ""; values = E.empty; types = E.empty; 
    constr = E.empty; label = E.empty }
    
let modules = 
  { current = current; opened = []; modules = E.empty }

let clear () =
  current.values <- E.empty; current.types <- E.empty;
  current.constr <- E.empty; current.label <- E.empty
						
let findfile filename =
  if Sys.file_exists filename then
    filename
  else if not(Filename.is_implicit filename) then
    raise(Cannot_find_file filename)
  else
    let rec find = function
      [] ->
        raise(Cannot_find_file filename)
    | a::rest ->
        let b = Filename.concat a filename in
          if Sys.file_exists b then b else find rest
    in find !load_path
    
let load_module modname =
  let name = String.uncapitalize_ascii modname in
    try
      let filename = findfile (name ^ ".zci") in
      let ic = open_in_bin filename in
        try
          let m = input_value ic in
            close_in ic;
            m
        with
          | End_of_file | Failure _ ->
              close_in ic;
              Printf.eprintf "Corrupted compiled interface file %s.\n\
                        Please recompile module %s first.\n" filename modname;
              raise Error
    with
      | Cannot_find_file(filename) ->
          Printf.eprintf "Cannot find the compiled interface file %s.\n"
            filename;
          raise Error
            
let find_module modname =
  try
    E.find modname modules.modules
  with
      Not_found ->
        let m = load_module modname in
          modules.modules <- E.add modname m modules.modules;
          m
            
let find where qualname =
    let rec findrec ident = function
      | [] -> raise Not_found
      | m :: l ->
          try { qualid = { qual = m.name; id = ident };
                info = where ident m }
          with Not_found -> findrec ident l in
      
      match qualname with
        | Modname({ qual = m; id = ident } as q) -> 
            let current = if current.name = m then current else find_module m in
            { qualid = q; info = where ident current }
        | Name(ident) -> findrec ident (current :: modules.opened)
            
(* exported functions *)
let open_module modname =
  let m = find_module modname in
  modules.opened <- m :: modules.opened
      
let initialize modname = 
  current.name <- modname;
  List.iter open_module !default_used_modules
  
let add_value f signature = 
  if E.mem f current.values then raise (Already_defined f);
  current.values <- E.add f signature current.values
  
let add_type f typ_desc =
  if E.mem f current.types then raise (Already_defined f);
  current.types <- E.add f typ_desc current.types
let add_constr f ty_res =
  if E.mem f current.constr then raise (Already_defined f);
  current.constr <- E.add f ty_res current.constr
let add_label f label_desc =
  if E.mem f current.label then raise (Already_defined f);
  current.label <- E.add f label_desc current.label

let find_value = find (fun ident m -> E.find ident m.values)
let find_type = find (fun ident m -> E.find ident m.types)
let find_constr = find (fun ident m -> E.find ident m.constr)
let find_label = find (fun ident m -> E.find ident m.label)
  
let write oc = output_value oc current

let qualify n = { qual = current.name; id = n }
let longname n = Modname({ qual = current.name; id = n })
let shortname { id = n } = n
let currentname longname =
  match longname with
    | Name(n) -> longname
    | Modname{ qual = q; id = id} -> 
        if current.name = q then Name(id) else longname
let qualident longname =
  match longname with | Name(n) -> qualify n | Modname(qid) -> qid
let current_module () = current.name
			  
