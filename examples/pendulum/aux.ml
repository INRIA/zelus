open Graphics

type key = Start | Freeze | Resume | Nothing

let input () =
  let rec myread v =
    if not (key_pressed ()) then v
    else myread (Some (read_key ())) in
  match myread None with
  | Some 's' -> Start
  | Some 'f' -> Freeze
  | Some 'q' -> exit 0
  | Some 'r' -> Resume
  | _ -> Nothing
