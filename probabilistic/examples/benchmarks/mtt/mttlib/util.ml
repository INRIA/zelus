open Owl

let tdiff = 1.0

let list_init = List.init

let cur_track_num = ref 0

let new_track_num _ = 
  let ret = !cur_track_num in
  cur_track_num := !cur_track_num + 1;
  ret

let birth_rate =  0.1
let death_rate = 0.02

let p_dead = exp (-. tdiff *. death_rate)

let lambda_new = birth_rate *. tdiff

let mu_new = 
  Mat.of_arrays [| [| 0.; |];
                   [| 0.; |];
                   [| 0.; |];
                   [| 0.; |]; |]

let sigma_new = 
  Mat.of_arrays [| [| 1.0; 0.0; 0.0; 0.0; |];
                   [| 0.0; 1.0; 0.0; 0.0; |];
                   [| 0.0; 0.0; 0.001; 0.0; |];
                   [| 0.0; 0.0; 0.0; 0.001; |]; |]

let a_u = 
  Mat.of_arrays [| [| 1.0; 0.0; tdiff; 0.0 |];
                   [| 0.0; 1.0; 0.0; tdiff |];
                   [| 0.0; 0.0; 1.0; 0.0   |];          
                   [| 0.0; 0.0; 0.0; 1.0   |]; |]

let b_u = 
  Mat.of_arrays [| [| 0.; |];
                   [| 0.; |]; 
                   [| 0.; |]; 
                   [| 0.; |]; |]

let sigma_update = 
  Mat.of_arrays [| [| 0.01; 0.0; 0.0; 0.0 |];
                   [| 0.0; 0.01; 0.0; 0.0 |];
                   [| 0.0; 0.0;  0.1; 0.0 |];
                   [| 0.0; 0.0;  0.0; 0.1 |]; |]

let lambda_clutter = 1.

let mu_clutter = 
  Mat.of_arrays [| [| 0.; |];
                   [| 0.; |]; |]

let proj_pos =
  Mat.of_arrays [| [| 1.0; 0.0; 0.0; 0.0 |];
                   [| 0.0; 1.0; 0.0; 0.0 |]; |]

let sigma_obs =
  Mat.of_arrays [| [| 1.0; 0.0 |];
                   [| 0.0; 1.0 |]; |]

let sigma_clutter = 
  Mat.of_arrays [| [| 10.0; 0.0 |];
                   [| 0.0; 10.0 |]; |]

let shuffle x = 
  let arr = Array.of_list x in
  for n = Array.length arr - 1 downto 1 do
    let k = Random.int (n + 1) in
    let tmp = arr.(n) in
    arr.(n) <- arr.(k);
    arr.(k) <- tmp
  done;
  Array.to_list arr

let ( *@ ) = Mat.( *@ )
let ( +@ ) = Mat.add

let string_of_tr vec_lst =
  "[" ^
  String.concat "," (List.map (fun (num, vec) ->
    "(" ^ string_of_int num ^ ", " ^ string_of_float (Mat.get vec 0 0) ^ ", " ^ 
    string_of_float (Mat.get vec 1 0) ^ ")"
  ) vec_lst)
  ^ "]" 

let string_of_vec2_list vec_lst =
  "[" ^
  String.concat "," (List.map (fun vec ->
    "(" ^ string_of_float (Mat.get vec 0 0) ^ ", " ^ 
    string_of_float (Mat.get vec 1 0) ^ ")"
  ) vec_lst)
  ^ "]" 

let string_of_int_list lst =
  "[" ^
  String.concat "," (List.map (fun i ->
    string_of_int i
  ) lst) ^
  "]\n"

let string_of_vec2 vec = 
  "(" ^ string_of_float (Mat.get vec 0 0) ^ ", " ^ 
  string_of_float (Mat.get vec 1 0) ^ ")"

let dist (v1 : Mat.mat) (v2 : Mat.mat) : float =
  let diff = Mat.sub v1 v2 in
  sqrt (Mat.get (Mat.dot (Mat.transpose diff) diff) 0 0)

module TrMap = Map.Make(Int)
type tr_map = int TrMap.t

let match_tostring (matching : tr_map) (num : int) : string =
  (String.concat "\n" (List.map (fun (i,j) ->
    (string_of_int i) ^ " -> " ^ (string_of_int j)
  ) (TrMap.bindings matching))) ^ "\n"

let thresh = 5.0

exception Match_error

let empty_matching : tr_map = TrMap.empty

(* cost : Cost matrix with cols >= rows *)
(* from http://csclab.murraystate.edu/~bob.pilgrim/445/munkres.html *)
let optimal_assignment (cost : Mat.mat) : (int * int) list =
  let rows = Mat.row_num cost in
  let cols = Mat.col_num cost in
  (assert (cols >= rows));

  let mask : int array = Array.init (rows * cols) (fun _ -> 0) in
  let get_mask i j = Array.get mask (i * cols + j) in
  let set_mask i j v = Array.set mask (i * cols + j) v in

  let row_cover : bool array = Array.init (rows) (fun _ -> false) in
  let col_cover : bool array = Array.init (cols) (fun _ -> false) in

  let print_debug _ =
    print_string "cost:\n";
    Mat.print cost;
    print_string "mask:\n";
    for i = 0 to rows - 1 do
      for j = 0 to cols - 1 do
        print_string (string_of_int (get_mask i j) ^ ", ")
      done;
      print_string "\n"
    done;
    print_string "row_cover:\n";
    for i = 0 to rows - 1 do
      print_string (string_of_bool (Array.get row_cover i) ^ ", ")
    done;
    print_string "\ncol_cover:\n";
    for j = 0 to cols - 1 do
      print_string (string_of_bool (Array.get col_cover j) ^ ", ")
    done;
    print_string "\n"
  in

  let find_noncovered_zero _ =
    let ret = ref None in
    for i = 0 to rows - 1 do
      for j = 0 to cols - 1 do
        if Mat.get cost i j = 0. && 
           Array.get row_cover i = false &&
           Array.get col_cover j = false then
         ret := Some (i,j)
        else ()
      done
    done;
    !ret
  in

  let star_in_row i =
    let ret = ref None in
    for j = 0 to cols - 1 do
      if get_mask i j = 1 then
        ret := Some(j)
      else ()
    done;
    !ret
  in

  let find_star_in_col j =
    let ret = ref None in
    for i = 0 to rows - 1 do
      if get_mask i j = 1 then
        ret := Some(i)
      else ()
    done;
    !ret
  in

  let find_prime_in_row i =
    let ret = ref None in
    for j = 0 to cols - 1 do
      if get_mask i j = 2 then
        ret := Some(j)
      else ()
    done;
    !ret
  in

  let rec augment_path path =
    match path with
    | [] -> ()
    | (i, j) :: ret ->
      begin if get_mask i j = 1 then
        set_mask i j 0
      else 
        set_mask i j 1
      end;
      augment_path ret
  in

  let clear_covers _ =
    for i = 0 to rows - 1 do
      Array.set row_cover i false
    done;
    for j = 0 to cols - 1 do
      Array.set col_cover j false
    done
  in

  let erase_primes _ =
    for i = 0 to rows - 1 do
      for j = 0 to cols - 1 do
        if get_mask i j = 2 then
          set_mask i j 0
        else ()
      done
    done
  in

  let find_smallest _ =
    let ret = ref infinity in
    for i = 0 to rows - 1 do
      for j = 0 to cols - 1 do
        let cur = Mat.get cost i j in
        if cur < !ret && not (Array.get row_cover i) && not (Array.get col_cover j) then
          ret := cur
        else
          ()
      done
    done;
    !ret
  in

  let rec step_1 _ =
    (*print_string "step_1\n";
    print_debug ();*)
    for i = 0 to rows - 1 do
      let max_in_row = ref infinity in
      for j = 0 to cols - 1 do
        let c = Mat.get cost i j in
        if c < !max_in_row then
          max_in_row := c
        else
          ()
      done;
      assert (!max_in_row < infinity);
      for j = 0 to cols - 1 do
        Mat.set cost i j ((Mat.get cost i j) -. !max_in_row)
      done;
    done;
    step_2 ()
  and step_2 _ =
    (*print_string "step_2\n";
    print_debug ();*)
    for i = 0 to rows - 1 do
      for j = 0 to cols - 1 do
        if Mat.get cost i j = 0. && 
           not (Array.get row_cover i) && 
           not (Array.get col_cover j) then (
          set_mask i j 1;
          Array.set row_cover i true;
          Array.set col_cover j true
        ) else ()
      done
    done;
    for i = 0 to rows - 1 do
      Array.set row_cover i false;
    done;
    for j = 0 to cols - 1 do
      Array.set col_cover j false;
    done;
    step_3 ()
  and step_3 _ =
    (*print_string "step_3\n";
    print_debug ();*)
    for i = 0 to rows - 1 do
      for j = 0 to cols - 1 do
        if get_mask i j = 1 then
          Array.set col_cover j true
        else ()
      done
    done;
    let colcount = ref 0 in
    for j = 0 to cols - 1 do
      if Array.get col_cover j then
        colcount := !colcount + 1
      else ()
    done;
    if (!colcount >= cols || !colcount >= rows) then
      step_7 ()
    else
      step_4 ()
  and step_4 _ =
    (*print_string "step_4\n";
    print_debug ();*)

    let is_done = ref false in
    while not !is_done do
      let zero = find_noncovered_zero () in
      match zero with
      | None ->
        is_done := true;
        step_6 ()
      | Some (i, j) ->
        set_mask i j 2;
        match star_in_row i with
        | None ->
          begin
            is_done := true;
            step_5 i j
          end
        | Some j_star ->
          begin
            Array.set row_cover i true;
            Array.set col_cover j_star false;
          end
    done
  and step_5 init_path_i init_path_j =
    (*print_string "step_5\n";
    print_debug ();*)

    let path = ref [ (init_path_i, init_path_j) ] in
    let cur_i = ref init_path_i in
    let cur_j = ref init_path_j in
    let is_done = ref false in
    while not !is_done do
      match find_star_in_col !cur_j with
      | None -> is_done := true
      | Some i ->
        cur_i := i;
        path := (!cur_i, !cur_j) :: !path;
      if not !is_done then
        match find_prime_in_row !cur_i with
        | None -> assert false
        | Some j ->
          cur_j := j;
          path := (!cur_i, !cur_j) :: !path
      else ()
    done;
    augment_path !path;
    clear_covers ();
    erase_primes ();
    step_3 ()
  and step_6 _ =
    (*print_string "step_6\n";
    print_debug ();*)

    let minval = find_smallest () in
    for i = 0 to rows - 1 do
      for j = 0 to cols - 1 do
        begin if Array.get row_cover i then
          Mat.set cost i j (Mat.get cost i j +. minval)
        else
          ()
        end;
        begin if not (Array.get col_cover j) then
          Mat.set cost i j (Mat.get cost i j -. minval)
        else
          ()
        end;
      done
    done;
    step_4 ()
  and step_7 _ = 
    (*print_string "step_7\n";
    print_debug ();*)
    () 
  in

  step_1 ();

  let ret = ref [] in
  for i = 0 to rows - 1 do
    for j = 0 to cols - 1 do
      if get_mask i j = 1 then
        ret := (i, j) :: !ret
      else ()
    done
  done;
  !ret

let  bignum = 1000000000.



(* returns (distance, matches, false_positives, misses, mismatches, objects, and new map)*)
let matching_helper   (prev_matching : tr_map) 
                      (truth : (int * Mat.mat) list)
                      (hyp : (int * Mat.mat) list) : 
                      ((float * int * int * int * int * int) * tr_map) =
                 
  let sum_dist = ref 0. in
  let num_matches = ref 0 in
  let false_positives = ref 0 in
  let mismatches = ref 0 in
  let misses = ref 0 in

  let truth_a = Array.of_list truth in
  let hyp_a = Array.of_list hyp in

  let init_matching : tr_map ref = ref TrMap.empty in
  for tr = 0 to Array.length truth_a - 1 do
    let (i, vec) = Array.get truth_a tr in
    match TrMap.find_opt i prev_matching with
    | None -> ()
    | Some j ->
      try
        let other_vec = List.assoc j hyp in
        if dist vec other_vec < thresh then
          init_matching := TrMap.add i j !init_matching
        else
          ()
      with Not_found -> ()
  done;

  let best_matching : tr_map ref = ref !init_matching in
  let cmat = Mat.zeros (Array.length truth_a) (Array.length hyp_a) in

  for i = 0 to Array.length truth_a - 1 do
    for j = 0 to  Array.length hyp_a - 1 do
      let (i', vec) = Array.get truth_a i in
      let (j', other_vec) = Array.get hyp_a j in
      if dist vec other_vec >= thresh then
        Mat.set cmat i j bignum
      else if TrMap.exists (fun i'' j'' -> i'' = i' && j'' = j') !init_matching then
        Mat.set cmat i j 0.
      else if TrMap.exists (fun i'' j'' -> i'' = i' || j'' = j') !init_matching then
        Mat.set cmat i j bignum
      else
        Mat.set cmat i j (dist vec other_vec)
    done
  done;

  if Array.length hyp_a >= Array.length truth_a then begin
    let assoc = optimal_assignment cmat in
    let rec compute_best_matching assoc =
      match assoc with
      | [] -> ()
      | (x, y) :: rst ->
        let (i, vec) = Array.get truth_a x in
        let (j, other_vec) = Array.get hyp_a y in
        if dist vec other_vec < thresh then
          best_matching := TrMap.add i j !best_matching
        else ();
        compute_best_matching rst
    in
    compute_best_matching assoc
  end else begin
    let assoc = optimal_assignment (Mat.transpose cmat) in
    let rec compute_best_matching assoc =
      match assoc with
      | [] -> ()
      | (y, x) :: rst ->
        let (i, vec) = Array.get truth_a x in
        let (j, other_vec) = Array.get hyp_a y in
        if dist vec other_vec < thresh then
          best_matching := TrMap.add i j !best_matching
        else ();
        compute_best_matching rst
    in
    compute_best_matching assoc
  end;

  (*
  print_string ("prev_matching:\n");
  print_string (match_tostring prev_matching 0);
  print_string ("init_matching:\n");
  print_string (match_tostring !init_matching 0);
  print_string ("best_matching:\n");
  print_string (match_tostring !best_matching 0);
  *)

  let final_match = TrMap.merge (fun i jo jo' ->
    match jo, jo' with
    | (None, None) -> 
      (*print_string ("Neither has i:" ^ (string_of_int i) ^ "\n");*)
      None
    | (Some j, None) -> 
      (*print_string ("Init matching has i: " ^ string_of_int i ^ 
                    " j: " ^ string_of_int j ^ "\n");*)
      None
    | (None, Some j') -> 
      (*print_string ("Best matching has i: " ^ string_of_int i ^ 
                    " j': " ^ string_of_int j' ^ "\n");*)
      let vec = List.assoc i truth in
      let other_vec = List.assoc j' hyp in
      sum_dist := !sum_dist +. (dist vec other_vec);
      num_matches := !num_matches + 1;
      Some j'
    | (Some j, Some j') ->
      (*(print_string ("Conflict! i: " ^ string_of_int i ^ 
                    ", j: " ^ string_of_int j ^
                    ", j': " ^ string_of_int j' ^ "\n"));*)
      let vec = List.assoc i truth in
      let other_vec = List.assoc j' hyp in
      sum_dist := !sum_dist +. (dist vec other_vec);
      num_matches := !num_matches + 1;
      if j = j' then
        Some j'
      else begin
        mismatches := !mismatches + 1;
        Some j'
      end
  ) prev_matching !best_matching in

  misses := Array.length truth_a - TrMap.cardinal final_match;
  false_positives := Array.length hyp_a - TrMap.cardinal final_match;

  (*
  print_string ("num_matches: " ^ string_of_int !num_matches ^ "\n");
  print_string ("misses: " ^ string_of_int !misses ^ "\n");
  print_string ("false_positives: " ^ string_of_int !false_positives ^ "\n");
  print_string ("mismatches: " ^ string_of_int !mismatches ^ "\n");
  *)

  ((!sum_dist, 
   !num_matches, 
   !false_positives, 
   !misses, 
   !mismatches, 
   Array.length truth_a),
   final_match)

let matching (prev_matching : tr_map) 
             (truth : (int * Mat.mat) list)
             (hyp : (int * Mat.mat) list) : 
             ((float * int * int * int * int * int) * tr_map) =
  if List.length truth = 0 then begin
    if List.length hyp = 0 then
      ((0., 0, 0, 0, 0, 0), TrMap.empty)
    else
      ((0., 0, List.length hyp, 0, 0, 0), TrMap.empty)
  end else begin
    if List.length hyp = 0 then
      ((0., 0, 0, List.length truth, 0, List.length truth), TrMap.empty)
    else
      matching_helper prev_matching truth hyp
  end
 
