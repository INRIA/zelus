(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2021 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* check the compiler *)

let compiler = "../compiler/zeluc.exe -I ../_build/default/lib/std/"

let verbose = ref false

let dir_list = ["good"; "bad"]
             
(* remove all files in [rep_list] *)
let clean rep_list =
  List.iter
    (fun d ->
      let c = "rm -f -r " ^ d ^ "/*.obc " ^ d ^ "/*.front "
              ^ d ^ "/*.zci " ^ d ^ "/*.ml " ^ d ^ "/*.cmi " ^ d ^ "*.cmo" in
      if !verbose then Printf.fprintf stdout "%s\n" c;
      ignore (Sys.command c))
    rep_list

let clean () = clean dir_list

let files dir =
  let files = Array.to_list (Sys.readdir dir) in
  let files =
    List.filter (fun file -> Filename.check_suffix file ".zlus") files in
  let files =
    List.sort String.compare files in
  List.map
    (fun file -> Filename.concat dir (Filename.chop_suffix file ".zlus")) files

let one file =
  let options = "-i -ic -ii" in
  let c =
    compiler ^ " " ^ options ^ " " ^ file ^ ".zlus" ^
      " > " ^ file ^ ".front " ^ "2>&1" in
  if !verbose then Printf.fprintf stdout "%s\n" c;
  let status =
    try
      Sys.command c
    with
    | x -> Printf.fprintf stdout "%s\n" (Printexc.to_string x); 1 in
  Printf.fprintf stdout "--%s:\tfront %s\n"
    file (if status = 0 then "ok"
          else "fail: see " ^ file ^ ".front");
  if !verbose then ignore (Sys.command ("cat " ^ file ^ ".front"));
  let ok = if status = 0 then 1 else 0 in
  ok

      
let several f_list =
  let score = List.fold_left (fun score file -> (one file) + score) 0 f_list in
  let max = List.length f_list in
  let percent = (100 * score) / max in
  Printf.fprintf stdout "Front-end:\t\t%d\t/\t%d\t(%%%d)\n"
    score max percent

let one file =
  let file = if Filename.check_suffix file ".zlus"
             then Filename.chop_suffix file ".zlus" else file in
  ignore (one file)
             
let good () =
  let f_list = files "good" in
  several f_list

let bad () =
  let f_list = files "bad" in
  several f_list


let doc_verbose = "\tVerbose mode"
let doc_clean = "\tClean"
let doc_good = "\tCheck good programs"
let doc_bad = "\tCheck bad programs"
let errmsg = "Options are:"
        
let main () =
  try
    Arg.parse
      (Arg.align
         [ "-v", Arg.Set verbose, doc_verbose;
           "-clean", Arg.Unit clean, doc_clean;
           "-bad", Arg.Unit bad, doc_bad;
           "-good", Arg.Unit good, doc_good])
      one
      errmsg
  with
    _ -> exit 2
       
let _ = main ()
let _ = exit 0
