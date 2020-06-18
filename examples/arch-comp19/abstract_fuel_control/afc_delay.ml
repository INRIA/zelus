module BoundedQueue =
struct
  type 'a t = {
    queue : 'a array;
    mutable length : int;
    mutable start : int;
  }

  let make n default = {
    queue = Array.make n default;
    length = 0;
    start = 0;
  }

  let length this = this.length
  let get this i =
    if i > Array.length this.queue then raise (Invalid_argument "index out of bounds");
    let i' = (this.start + i) mod (Array.length this.queue) in
    this.queue.(i')
  let set this i el =
    if i > Array.length this.queue then raise (Invalid_argument "index out of bounds");
    let i' = (this.start + i) mod (Array.length this.queue) in
    this.queue.(i') <- el

  let to_array this =
    let arr = Array.make this.length this.queue.(0) in
    for i = 0 to this.length - 1 do
      arr.(i) <- get this i
    done; arr

  let incr_head this =
    this.start <- (this.start + 1) mod (Array.length this.queue)

  (* if queue is full, will overwrite oldest values *)
  let enqueue this el =
    if this.length < Array.length this.queue then begin
      set this this.length el;
      this.length <- this.length + 1
    end else begin
      incr_head this;
      set this (this.length - 1) el;
    end

  let dequeue this =
    if this.length > 0 then
      let el = get this 0 in
      incr_head this;
      this.length <- this.length - 1;
      el
    else
      raise (Invalid_argument "cannot dequeue an empty queue")

  let peek this =
    if this.length > 0 then get this 0
    else raise (Invalid_argument "cannot peek at empty queue")
end

module Delay =
struct
  type 'a t = {
    max_delay: float;
    buffer_t : float BoundedQueue.t;
    buffer_v : 'a BoundedQueue.t;
    default  : 'a
  }

  let make buffer_size max_delay default = {
    max_delay;
    buffer_t = BoundedQueue.make buffer_size 0.;
    buffer_v = BoundedQueue.make buffer_size default;
    default;
  }

  let record this (t, v) =
    (* Printf.printf "record %g %g\n" t v; *)
    BoundedQueue.enqueue this.buffer_t t;
    BoundedQueue.enqueue this.buffer_v v

  (* vec is an ordered float array
   * returns i such that vec.(i) < v < vec.(i+1) (or i = 0 or i = length vec) *)
  let ifind v queue =
    let rec aux start_i end_i =
      if start_i = end_i then start_i
      else
        let i = (start_i + end_i) / 2 in
        let v_i = BoundedQueue.get queue i in
        let v_ip1 = BoundedQueue.get queue (i+1) in
        if v_i < v && v < v_ip1 then i
        else if v_i > v then aux start_i (max 0 (i-1))
        else if v > v_ip1 then
          aux (min (BoundedQueue.length queue - 1) (i+1)) end_i
        else assert false
    in aux 0 (BoundedQueue.length queue - 1)

  (* linear interpolatiion, x1 <= xi <= x2 *)
  let interp x1 x2 val1 val2 xi =
    if val1 = val2 then val1
    else
    (x2 -. xi) /. (x2 -. x1) *. val1 +.
    (xi -. x1) /. (x2 -. x1) *. val2

  (* linear extrapolation, x1 <= x2 <= xi OR xi <= x1 <= x2 *)
  let extrap x1 x2 val1 val2 xi =
    let slope = (val2 -. val1) /. (x2 -. x1) in
    let dif = slope *. (xi -. x1) in
    val1 +. dif

  (* LOOKUP FUNCTIONS:
   * These functions implement lookup tables that performs linear interpolation
   * and extrapolation. *)

  let interp1 this t =
    let line = this.buffer_t in
    let vals = this.buffer_v in
    try
      let li = ifind t line in
      (* Printf.printf "interp1\n\t[%s]\n\t[%s]\n\t %g, li = %d\n"
        (String.concat ";" (Array.to_list (Array.map string_of_float (BoundedQueue.to_array line))))
        (String.concat ";" (Array.to_list (Array.map string_of_float (BoundedQueue.to_array vals))))
        t li; *)
      if li = 0 then
        extrap (BoundedQueue.get line 0) (BoundedQueue.get line 1)
          (BoundedQueue.get vals 0) (BoundedQueue.get vals 1) t
      else if li = (BoundedQueue.length line) then
        extrap (BoundedQueue.get line (li - 2))
          (BoundedQueue.get line (li - 1))
          (BoundedQueue.get vals (li - 2)) (BoundedQueue.get vals (li - 1)) t
      else
        interp (BoundedQueue.get line (li - 1)) (BoundedQueue.get line li)
          (BoundedQueue.get vals (li - 1)) (BoundedQueue.get vals li) t
    with Invalid_argument s ->
      let li = ifind t line in
      print_string "Invalid argument (Delay.interp1): "; print_string s;
      print_newline ();
      print_int li; print_string " / "; print_int (BoundedQueue.length line);
      print_string ", "; print_float t; print_newline ();
      exit 1

  let get this (t, v, delay) =
    let delay = if delay < 0. then begin
      Printf.eprintf "WARNING: Delay.get got delay = %g, it has been clipped to 0\n" delay;
      0.
    end else
        min delay this.max_delay
    in


    if delay = 0. then v
    else
      let t' = t -. delay in
      let first_t = BoundedQueue.peek this.buffer_t in
      (* Printf.printf "get (%g, %g, %g), first_t = %g, t' = %g, t' < first_t: %b\n" t v delay first_t t' (t' < first_t); *)
      if t' < first_t then this.default
      else interp1 this t'
end

type 'a delay_t = 'a Delay.t
let make_delay = Delay.make
let record_delay = Delay.record
let get_delay = Delay.get
