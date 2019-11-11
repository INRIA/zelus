open Owl
open Mttlib
open Util

let v1 = Mat.of_arrays [| [| 0. |];
                          [| 1. |]; |];;

let v2 = Mat.of_arrays [| [| 1. |];
                          [| 1. |] |];;

print_string ("dist(" ^ string_of_vec2 v1 ^ ", " ^ string_of_vec2 v2 ^ ") = " ^ 
string_of_float (dist v1 v2) ^"\n")

let v3 = Mat.of_arrays [| [| 0. |];
                          [| 1. |]; |];;

let v4 = Mat.of_arrays [| [| 1. |];
                          [| 0. |] |];;

print_string ("dist(" ^ string_of_vec2 v3 ^ ", " ^ string_of_vec2 v4 ^ ") = " ^ 
string_of_float (dist v3 v4) ^"\n");;

let assoc_list_tostring lst =
  "[" ^ (String.concat "," (List.map (fun (x,y) ->
    "(" ^ string_of_int x ^ ", " ^ string_of_int y ^ ")"
  ) lst)) ^ "]"

let cmat1 = Mat.of_arrays [| [| 1. ;  2. ; 3. |];
                             [| 2. ;  4. ; 6. |];
                             [| 3. ;  6. ; 9. |] |];;

print_string "cmat1:\n";;
Mat.print cmat1;;
print_string "matching of cmat1:\n";;
print_string (assoc_list_tostring (optimal_assignment cmat1) ^ "\n");;

let cmat2 = Mat.of_arrays [| [| 1. ;  2. ; 3. ; 4. |];
                             [| 2. ;  4. ; 6. ; 8. |];
                             [| 3. ;  6. ; 9. ; 12.|] |];;

print_string "cmat2:\n";;
Mat.print cmat2;;
print_string "matching of cmat2:\n";;
print_string (assoc_list_tostring (optimal_assignment cmat2) ^ "\n");;


let match0 = empty_matching;;

print_string "match0\n";;
print_string (match_tostring match0 5);;

let truth0 = [ (1, v1) ; (2, v2) ];;
let hyp0 = [ (1, v2) ; (2, v1) ];;

print_string "truth0:\n";;
print_string (string_of_tr truth0 ^ "\n");;

print_string "hyp0:\n";;
print_string (string_of_tr hyp0 ^ "\n");;

let motp0, mota0, match1 = matching match0 truth0 hyp0;;

print_string "motp0:\n";;
print_string (string_of_float motp0 ^ "\n");;

print_string "mota0:\n";;
print_string (string_of_float mota0 ^ "\n");;

print_string "match1:\n";;
print_string (match_tostring match1 5);;

let truth1 = [ (1, v1) ; (2, v2) ];;
let hyp1 = [ (1, v2) ; (2, v1) ; (3, v4) ];;

print_string "truth1:\n";;
print_string (string_of_tr truth1 ^ "\n");;

print_string "hyp1:\n";;
print_string (string_of_tr hyp1 ^ "\n");;

let motp1, mota1, match2 = matching match1 truth1 hyp1;;

print_string "motp1:\n";;
print_string (string_of_float motp1 ^ "\n");;

print_string "mota1:\n";;
print_string (string_of_float mota1 ^ "\n");;

print_string "match2:\n";;
print_string (match_tostring match2 5);;

let truth2 = [ (1, v1) ; (2, v2) ; (3, v4) ];;
let hyp2 = [ (1, v2) ; (2, v1) ];;

print_string "truth2:\n";;
print_string (string_of_tr truth2 ^ "\n");;

print_string "hyp2:\n";;
print_string (string_of_tr hyp2 ^ "\n");;

let motp2, mota2, match3 = matching match2 truth2 hyp2;;

print_string "motp2:\n";;
print_string (string_of_float motp2 ^ "\n");;

print_string "mota2:\n";;
print_string (string_of_float mota2 ^ "\n");;

print_string "match3:\n";;
print_string (match_tostring match3 5);;

let v5 = Mat.of_arrays [| [| 10. |];
                          [| 11. |]; |];;

let v6 = Mat.of_arrays [| [| 15. |];
                          [| 16. |] |];;

let v7 = Mat.of_arrays [| [| 9. |];
                          [| 10. |]; |];;

let v8 = Mat.of_arrays [| [| 16. |];
                          [| 17. |] |];;

let truth3 = [ (1, v5); (2, v6) ];;
let hyp3 = [ (1, v7); (2, v8) ];;

print_string "truth3:\n";;
print_string (string_of_tr truth3 ^ "\n");;

print_string "hyp3:\n";;
print_string (string_of_tr hyp3 ^ "\n");;

let motp3, mota3, match4 = matching match3 truth3 hyp3;;

print_string "motp3:\n";;
print_string (string_of_float motp3 ^ "\n");;

print_string "mota3:\n";;
print_string (string_of_float mota3 ^ "\n");;

print_string "match4:\n";;
print_string (match_tostring match4 5);;

let truth4 = [ (1, v5); (2, v6) ];;
let hyp4 = [ (1, v7); (2, v5) ];;

print_string "truth4:\n";;
print_string (string_of_tr truth4 ^ "\n");;

print_string "hyp4:\n";;
print_string (string_of_tr hyp4 ^ "\n");;

let motp4, mota4, match5 = matching match4 truth4 hyp4;;

print_string "motp4:\n";;
print_string (string_of_float motp4 ^ "\n");;

print_string "mota4:\n";;
print_string (string_of_float mota4 ^ "\n");;

print_string "match5:\n";;
print_string (match_tostring match5 5);;

let truth5 = [ (1, v5); (2, v5); (3, v5) ];;
let hyp5 = [ (1, v5); (2, v5); (3, v5) ];;

print_string "truth5:\n";;
print_string (string_of_tr truth5 ^ "\n");;

print_string "hyp5:\n";;
print_string (string_of_tr hyp5 ^ "\n");;

let init_match = TrMap.add 1 3 TrMap.empty
let motp5, mota5, match6 = matching init_match truth5 hyp5 ;;

print_string "motp5:\n";;
print_string (string_of_float motp5 ^ "\n");;

print_string "mota5:\n";;
print_string (string_of_float mota5 ^ "\n");;

print_string "match6:\n";;
print_string (match_tostring match6 5);;

