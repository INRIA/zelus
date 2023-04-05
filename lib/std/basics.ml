let stdform_of_float pref suf f =
  Printf.sprintf
    (Scanf.format_from_string
       (Printf.sprintf "%%%d.%de" pref suf)
       "%e")
    f

let output_line output_item out ss =
  let pr s = (output_string out "\t"; output_item out s) in
  if List.length ss = 0 then ()
  else (output_item out (List.hd ss); List.iter pr (List.tl ss));
  output_string out "\n"

let output_strings out ss = output_line output_string out ss

let output_quoted_strings out ss =
  output_line (fun oc s -> (Printf.fprintf oc "\"%s\"" s; flush oc)) out ss
let output_floats out ss =
  output_line (fun oc s -> (Printf.fprintf oc "%.15e" s; flush oc)) out ss

(* Compare two floats for equality, see:
 * http://www.cygnus-software.com/papers/comparingfloats/comparingfloats.htm
 *)
let float_eq max_relative_error f1 f2 =
  if abs_float (f1 -. f2) < min_float
  then true (* absolute error check for numbers around to zero *)
  else
    let rel_error =
      if abs_float f1 > abs_float f2
      then abs_float ((f1 -. f2) /. f1)
      else abs_float ((f1 -. f2) /. f2)
    in
    (rel_error <= max_relative_error)

(* 99.9999% accuracy *)
let (=~=) = float_eq 0.000001

let on x y = x && y

let bad_sgn e = if e = 0.0 then 0.0 else if e > 0.0 then 1.0 else -1.0

let exit n = exit n
		  
