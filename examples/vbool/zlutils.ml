type duration = float
type value = float
type input_type =
  | Zero
  | Constant of float (* value *)
  | Linear of float (* target value *)
type input_chunk = float * input_type (* duration * chunk type *)

let random_float (l, h) =
    let l,h = if l > h then (l, h) else (h, l) in
    Random.float (h -. l) +. l

let random_chunk (dur_low, dur_high) (value_low, value_high) =
    random_float (dur_low, dur_high),
    random_float (value_low, value_high)

let random_chunks n (dur_low, dur_high) (value_low, value_high) =
    let q = Queue.create () in
    for i = 0 to (n-1) do
      () = Queue.push (random_chunk (dur_low, dur_high) (value_low, value_high)) q
    done;
    q

let rec delete_in_list l i =
  if i = 0 then List.tl l else List.hd l :: delete_in_list (List.tl l) (i-1)
let rec replace_in_list l i e =
  if i = 0 then e :: List.tl l else List.hd l :: replace_in_list (List.tl l) (i-1) e

let string_of_chunk (dur,value) =
  Printf.sprintf "(%.2f, %.2f)" dur value

let string_of_input inp =
  "[" ^
  String.concat ", " (
    List.rev (
      Queue.fold (fun acc chunk -> (string_of_chunk chunk) :: acc)
        [] inp)) ^
  "]"

let passed t = Printf.printf "OK: Reached maxt = %.2f\n" t; exit 0
let falsified t phi =
  Printf.printf "FALSIFIED: at t = %.2f with value %.2f\n" t phi; exit 1
