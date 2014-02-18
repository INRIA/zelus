(* #! /usr/bin/env ocamlscript *)

(*
 * Reads two data files; the first column in each containing the time and each
 * having the same number of columns. Returns a new datafile containing the
 * differences between corresponding columns against the time. The resulting
 * sample times are the union of the sample times from both files. Linear
 * interpolation is used to approximate values at instants that are sampled in
 * one file but not the other.
 *
 * Use to compare the outputs of simulation runs made using different systems or
 * solvers.
 *)

let printf = Printf.printf
let eprintf = Printf.eprintf
let delim = Str.regexp "[ \t\n]+"

let getline file =
  try
    let line = input_line file in
    match List.map float_of_string (Str.split delim line) with
    | t::vs -> t, vs
    | _ -> 0.0, []
  with End_of_file -> 0.0, []

let putline t vs1 vs2 =
  printf "%.15e" t;
  List.iter2 (fun x y -> printf "\t%.15e" (x -. y)) vs1 vs2;
  print_newline ()

let interpolate it (lt, lvs) (nt, nvs) =
  if it = nt then nvs
  else
    let dt = nt -. lt
    and i = it -. lt in
    List.map2 (fun lv nv -> lv +. i *. (nv -. lv) /. dt) lvs nvs

let main path1 path2 =
  let file1 = open_in path1 in
  let file2 = open_in path2 in

  let titles1 = Str.split delim (input_line file1) in
  let titles2 = Str.split delim (input_line file2) in

  if titles1 <> titles2 then begin
    eprintf "The titles in %s are different to those in %s.\n" path1 path2;
    List.iter2 (fun t1 t2 -> printf "\t%s\t%s\t%s\n" t1
                                 (if t1 = t2 then "=" else "<>") t2)
                 titles1 titles2;
    exit 1
  end;

  print_string "\"time\"";
  List.iter (printf "\t%s") (List.tl titles1);
  print_newline();

  let t1, vs1 = getline(file1) in
  let t2, vs2 = getline(file2) in

  if t1 <> 0.0 or t2 <> 0.0 then begin
    eprintf "The time values in both files must start at 0.0.\n\
             (%s starts at %e; %s starts at %e.)\n" path1 t1 path2 t2;
    exit 2
  end;

  if List.length vs1 <> List.length vs2 then begin
    eprintf "Both files must contain the same number of data columns.\n\
             (%s contains %d; %s contains %d.)\n"
             path1 (List.length vs1) path2 (List.length vs2);
    exit 3
  end;

  let rec loop last1 ((t1, vs1) as cur1) last2 ((t2, vs2) as cur2) =
    if vs1 = [] || vs2 = [] then ()
    else
      let ti = min t1 t2 in
      putline ti (interpolate ti last1 cur1) (interpolate ti last2 cur2);
      let last1, cur1 = if t1 <= t2 then cur1, getline file1 else last1, cur1
      and last2, cur2 = if t2 <= t1 then cur2, getline file2 else last2, cur2 in
      loop last1 cur1 last2 cur2
  in

  loop (0.0, []) (0.0, vs1) (0.0, []) (0.0, vs2);
  close_in file1; close_in file2

let () =
  if (Array.length Sys.argv != 3) then
    (prerr_endline "usage: diff_log FILE1 FILE2"; exit 1)
  else main Sys.argv.(1) Sys.argv.(2)

