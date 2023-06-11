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

(* an other version *)
(*
let read_key () =
  let r = ref  in
  ignore (Thread.create (fun () -> r := Some(Graphics.read_key ())) ());
  r

(* convert an option type into a Zelus signal. This is ugly *)
(* as it use the Obj.magic function. This is because signals *)
(* are not implemented as option type, as it was in LS, but as *)
(* a dependent pair. This is temporary, as long as sum types are not *)
(* provided in Zelus *)
let get s =
  (match !s with
  | None -> false, Obj.magic ()
  | Some(v) -> true, v

(* Then, this function would not block *)
let node input () =
  reset 
    init s = Aux.read_key ()  (* s est une promesse *)
   and
    present Aux.get(s)(v) -> emit c = v
  every false -> ?last c
*)
