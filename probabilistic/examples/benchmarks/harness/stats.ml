
let option_iter f o =
  begin match o with
    | Some x -> f x
    | None -> ()
  end

let array_flatten arr =
  let l1 = Array.length arr in
  let l2 = Array.length arr.(0) in
  let res = Array.make (l1 * l2) arr.(0).(0) in
  let k = ref 0 in
  for i = 0 to l1 - 1 do
    for j = 0 to l2 - 1 do
      res.(!k) <- arr.(i).(j);
      incr k;
    done
  done;
  res

let array_transpose arr =
  let l1 = Array.length arr in
  let l2 = Array.length arr.(0) in
  Array.init l2
    (fun i ->
       Array.init l1
         (fun j ->
            arr.(j).(i)))

let array_assoc x a =
  let res = ref None in
  Array.iter
    (fun (y, v) -> if x = y then res := Some v)
    a;
  begin match !res with
    | None -> raise Not_found
    | Some v -> v
  end


let stats (lower_quantile, middle_quantile, upper_quantile) arr =
  let len_i = Array.length arr in
  let len = float_of_int len_i in
  Array.sort compare arr;
  let upper_idx = min (len_i - 1) (truncate (len *. upper_quantile +. 0.5)) in
  let lower_idx = min (len_i - 1) (truncate (len *. lower_quantile +. 0.5)) in
  let middle_idx = min (len_i - 1) (truncate (len *. middle_quantile +. 0.5)) in
  (Array.get arr lower_idx, Array.get arr middle_idx, Array.get arr upper_idx)


let output_stats pgf_format file idx_label value_label stats  =
  let ch = open_out file in
  let fmt = Format.formatter_of_out_channel ch in
  Format.fprintf fmt
    "%s, %s lower quantile, median, upper quantile@."
    idx_label value_label;
  if not pgf_format then begin
    Array.iter
      (fun (idx, (low, mid, high)) ->
         Format.fprintf fmt "%d, %f, %f, %f@." idx low mid high)
      stats;
  end
  else begin
    Array.iter
      (fun (idx, (low, mid, high)) ->
         Format.fprintf fmt "%d   %f   %f   %f@." idx mid (mid -. low) (high -. mid))
      stats;
  end;
  close_out ch


let read_stats file =
  let ch = open_in file in
  let _ = input_line ch in
  let ic = Scanf.Scanning.from_channel ch in
  let acc = ref [] in
  begin try
      while true do
        let entry =
          Scanf.bscanf ic ("%d, %f, %f, %f\n")
            (fun idx low mid high -> (idx, (low, mid, high)))
        in
        acc := entry :: !acc

      done
    with End_of_file -> ()
  end;
  Array.of_list (List.rev !acc)
