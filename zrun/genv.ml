(* *********************************************************************)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* Environment global variables *)
open Misc
open Lident
open Global
   
module E = Map.Make (struct type t = string let compare = compare end)

exception Cannot_find_file of string

(* The current global environment *)
type 'a env =
  { name: string; (* the name of the module *)
    values: 'a E.t; (* the symbol table [name, entry] *)
  }
      
(* The current global environment and list of already opened modules *)
type 'a genv =
    { current: 'a env;      (* associated symbol table *)
      opened: 'a env list;  (* opened tables *)
      modules: 'a env E.t;  (* tables loaded in memory *)
    }

let findfile filename =
  if Sys.file_exists filename then filename
  else if not(Filename.is_implicit filename) then
    raise(Cannot_find_file filename)
  else
    let rec find = function
      | [] ->
         raise(Cannot_find_file filename)
      | a :: rest ->
         let b = Filename.concat a filename in
         if Sys.file_exists b then b else find rest
    in find !load_path
    
let load_module modname =
  let name = String.uncapitalize_ascii modname in
  try
    let filename = findfile (name ^ ".zlo") in
    let ic = open_in_bin filename in
    try
      let m = Marshal.from_channel ic in
      close_in ic;
      m
    with
    | End_of_file | Failure _ ->
       close_in ic;
       Printf.eprintf "Corrupted interface file %s.\n\
                       Please run module %s first.\n" filename modname;
       raise Misc.Error
  with
  | Cannot_find_file(filename) ->
     Printf.eprintf "Cannot find the interface file %s.\n"
       filename;
     raise Misc.Error
            
let find_module modname genv =
  try
    E.find modname genv.modules, genv
  with
    Not_found ->
    let m = load_module modname in
    m, { genv with modules = E.add modname m genv.modules }
            
(* Find the associated value of [qualname] in the list of currently *)
(* opened modules *)
let find qualname ({ current; opened } as genv) =
  let rec findrec ident = function
    | [] -> raise Not_found
    | { name; values } :: l ->
       try { qualid = { qual = name; id = ident };
             info = E.find ident values }, genv
       with Not_found -> findrec ident l in
  
  match qualname with
  | Modname({ qual; id } as q) -> 
     let current, genv =
       if current.name = qual then current, genv else find_module qual genv in
     let info = E.find id current.values in
     { qualid = q; info = info }, genv
  | Name(ident) -> findrec ident (current :: opened)
            
(* exported functions *)
let add_module genv m =
  { genv with opened = m :: genv.opened }

let open_module genv modname =
  let m, genv = find_module modname genv in
  { genv with opened = m :: genv.opened }
      
let initialize modname default_used_modules =
  let genv =
    { current = { name = modname; values = E.empty };
    opened = []; modules = E.empty } in
  List.fold_left open_module genv default_used_modules  
  
let add f pvalue ({ current } as genv) =
  let current =
    { current with values = E.add f pvalue current.values } in
  { genv with current = current }

let find qualname genv =
  let v, _ = find qualname genv in
  v
  
let write { current } oc = Marshal.to_channel oc current [Marshal.Closures]

