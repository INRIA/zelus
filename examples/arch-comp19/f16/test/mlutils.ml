let run_program = "cd ../python_model; python -c 'from Morellif16 import Morellif16; from sys import argv; args = list(map(float, argv[1:14])); print(Morellif16(*args))'"

let run_Morelli alpha beta de da dr p q r cbar b v xcg xcgref =
  let cmd = Printf.sprintf "%s %f %f %f %f %f %f %f %f %f %f %f %f %f"
      run_program alpha beta de da dr p q r cbar b v xcg xcgref
  in
  let inp = Unix.open_process_in cmd in
  let r = input_line inp in
  close_in inp;
  let v1 = ref 0. in
  let v2 = ref 0. in
  let v3 = ref 0. in
  let v4 = ref 0. in
  let v5 = ref 0. in
  let v6 = ref 0. in
  Scanf.sscanf r "(%f, %f, %f, %f, %f, %f)"
    (fun v1' v2' v3' v4' v5' v6' ->
       v1 := v1'; v2 := v2'; v3 := v3'; v4 := v4'; v5 := v5'; v6 := v6' );
    (!v1, !v2, !v3, !v4, !v5, !v6)

let rel_error f1 f2 =
  if abs_float (f1 -. f2) < min_float
  then 0. (* absolute error check for numbers around to zero *)
  else
    let rel_error =
      if abs_float f1 > abs_float f2
      then abs_float ((f1 -. f2) /. f1)
      else abs_float ((f1 -. f2) /. f2)
    in rel_error

let (=~=) f1 f2 = rel_error f1 f2 <= 0.0001

let print_results step
    (alpha, beta, el, ail, rdr, p, q, r, cbar, b, vt, xcg, xcgr)
    (cxt, cyt, czt, clt, cmt, cnt)
    (cxtP, cytP, cztP, cltP, cmtP, cntP) =
  Printf.printf "At step = %d " step;
  if (cxt =~= cxtP) &&  (cyt =~= cytP) &&  (czt =~= cztP) &&
     (clt =~= cltP) &&  (cmt =~= cmtP) &&  (cnt =~= cntP) then
    print_endline "OK"
  else begin
    print_endline "NOT OK";
    Printf.printf "With inputs:\n";
    Printf.printf "\t alpha = % 6.12f\n" alpha;
    Printf.printf "\t beta  = % 6.12f\n" beta;
    Printf.printf "\t el    = % 6.12f\n" el;
    Printf.printf "\t ail   = % 6.12f\n" ail;
    Printf.printf "\t rdr   = % 6.12f\n" rdr;
    Printf.printf "\t p     = % 6.12f\n" p;
    Printf.printf "\t q     = % 6.12f\n" q;
    Printf.printf "\t r     = % 6.12f\n" r;
    Printf.printf "\t cbar  = % 6.12f\n" cbar;
    Printf.printf "\t b     = % 6.12f\n" b;
    Printf.printf "\t vt    = % 6.12f\n" vt;
    Printf.printf "\t xcg   = % 6.12f\n" xcg;
    Printf.printf "\t xcgr  = % 6.12f\n" xcgr;
    print_newline ();
    Printf.printf "Got outputs:\n";
    Printf.printf "cxt:\t%- .12f\tvs. %- .12f\trel_error = % 2.12f\n" cxt cxtP (rel_error cxt cxtP);
    Printf.printf "cyt:\t%- .12f\tvs. %- .12f\trel_error = % 2.12f\n" cyt cytP (rel_error cyt cytP);
    Printf.printf "czt:\t%- .12f\tvs. %- .12f\trel_error = % 2.12f\n" czt cztP (rel_error czt cztP);
    Printf.printf "clt:\t%- .12f\tvs. %- .12f\trel_error = % 2.12f\n" clt cltP (rel_error clt cltP);
    Printf.printf "cmt:\t%- .12f\tvs. %- .12f\trel_error = % 2.12f\n" cmt cmtP (rel_error cmt cmtP);
    Printf.printf "cnt:\t%- .12f\tvs. %- .12f\trel_error = % 2.12f\n" cnt cntP (rel_error cnt cntP);
    print_newline (); print_newline ()
  end
