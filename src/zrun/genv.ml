(***********************************************************************)
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


(* Environment global variables *)
open Misc
open Lident
   
type 'a info = { qualid : Lident.qualident; info : 'a }

module E = Map.Make (struct type t = string let compare = compare end)

exception Cannot_find_file of string
    
exception Already_defined of string

(* The current global environment *)
type 'v env =
  { name: string; (* the name of the module *)
    values: 'v E.t; (* the symbol table [name, entry] - values *)
  }
      
(* The current global environment and list of already opened modules *)
type 'v genv =
    { current: 'v env;      (* associated symbol table *)
      opened: 'v env list;  (* opened tables *)
      modules: 'v env E.t;  (* tables loaded in memory *)
    }

(* debug info *)
let show { current; opened; modules } =
  let show_env { name; values } =
    (name, E.to_list values) in
  "current", show_env current,
  "opened", List.map show_env opened,
  "modules", List.map (fun (m, env) -> (m, show_env env)) (E.to_list modules)

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
let find where qualname ({ current; opened } as genv) =
  let rec findrec ident = function
    | [] -> raise Not_found
    | { name; values } :: l ->
       try { qualid = { qual = name; id = ident };
             info = E.find ident values }, genv
       with Not_found -> findrec ident l in
  
  match qualname with
  | Modname({ qual; id } as q) -> 
     let current, genv =
       if current.name = qual then current, genv 
       else find_module qual genv in
     let info = where id current in
     { qualid = q; info = info }, genv
  | Name(ident) -> findrec ident (current :: opened)
            
(* exported functions *)
let add_module genv m =
  { genv with opened = m :: genv.opened;
              modules = E.add m.name m genv.modules }

let open_module genv modname =
  let m, genv = find_module modname genv in
  { genv with opened = m :: genv.opened }

let try_to_open_module genv modname =
  let exists modname =
  try
    let name = String.uncapitalize_ascii modname in
    let _ = findfile (name ^ ".zlo") in true
  with
  | Cannot_find_file _ -> false in
  if exists modname then 
     let m, genv = find_module modname genv in
     { genv with opened = m :: genv.opened }
  else genv
      
let initialize modname default_used_modules =
  let genv =
    { current = { name = modname; values = E.empty };
    opened = []; modules = E.empty } in
  List.fold_left open_module genv default_used_modules  
  
let add f pvalue ({ current } as genv) =
  let current =
    { current with values = E.add f pvalue current.values } in
  { genv with current = current }

let find_value qualname genv =
  let v, _ = find (fun ident m -> E.find ident m.values) qualname genv in v

let write { current } oc = Marshal.to_channel oc current [Marshal.Closures]
    
let current { current } = current

let shortname { id = n } = n

let empty =
  let c_empty = { name = ""; values = E.empty } in
  { current = c_empty; opened = []; modules = E.empty }
