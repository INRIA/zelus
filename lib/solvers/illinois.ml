
include Solvers.ZerosInfrastructure

(* type of a session with the solver *)
(*  zx = g(t, c) yields the values of system zero-crossing expressions
    
    f0/t0 are the zero-crossing expression values at the last mesh point
    f1/t1 are the zero-crossing expression values at the next mesh point

    rightf_valid is false until f1/t1 is initialised. Since this involves a call
    to the root function g, it must be delayed to avoid triggering undesired
    side-effects; bothf_valid implies rightf_valid.

    bothf_valid is true when both f0/t0 and f1/t1 are valid and thus find
    can check for zero-crossings between them.

    roots is the array of booleans returned to callers to indicate on which
    expressions zero-crossings have been detected.

    calc_zc determines the kind of zero-crossings to seek and report.

    fta and ftb are temporary arrays used when searching for zero-crossings.
    They are kept in the session as an optimisation to avoid having to
    continually create and destroy arrays.
 *)
type 'cvec t = {
    g : float -> 'cvec -> zxvec -> unit;
    mutable rightf_valid : bool;
    mutable bothf_valid  : bool;

    mutable f0 : zxvec;
    mutable t0 : float;

    mutable f1 : zxvec;
    mutable t1 : float;

    mutable roots : zvec;
    mutable calc_zc : float -> float -> int;

    mutable fta : zxvec;
    mutable ftb : zxvec;
  }

let reinit s t c =
  s.t1 <- t;
  s.rightf_valid <- false;
  s.bothf_valid  <- false

let init (nroots, g) c =
  let s =
    {
        g = g;
        rightf_valid = false;
        bothf_valid  = false;

        f0 = create nroots;
        t0 = 0.0;

        f1 = create nroots;
        t1 = 0.0;

        fta = create nroots;
        ftb = create nroots;

        roots = zvec_create nroots;
        calc_zc = get_check_root Up;
    }
  in
  reinit s 0.0 c;
  s

let num_roots { f0 } = length f0

(* Called from find when bothf_valid = false to initialise f1. This cannot be
   done in init/reinit where g is not yet guaranteed to be side-effect free. *)
let init_mesh ({ g; f1 = f1; t1 = t1 } as s) c =
  g t1 c f1;   (* fill f1, because it is immediately copied into f0 by next_mesh *)
  s.rightf_valid <- true

(* f0/t0 take the previous values of f1/t1, f1/t1 are refreshed by g *)
let next_mesh ({ g; f0 = f0; f1 = f1; t1 = t1; roots } as s) t c =

  (* swap f0 and f1; f0 takes the previous value of f1 *)
  s.f0 <- f1;
  s.t0 <- t1;
  s.f1 <- f0;
  s.t1 <- t;

  (* calculate a new value for f1 *)
  g t c s.f1;
  s.bothf_valid <- true

type root_interval = SearchLeft | FoundMid | SearchRight

let resolve_intervals r1 r2 =
  match r1, r2 with
  | SearchLeft, _  | _, SearchLeft -> SearchLeft
  | FoundMid, _    | _, FoundMid   -> FoundMid
  | SearchRight, _                 -> SearchRight

(* Check for zero-crossings between f_left and f_mid, filling roots with the
   intermediate results and returning:

      SearchLeft   zero-crossing in (f_left, f_mid)
      FoundMid     no zero-crossing in (f_left, f_mid)
                   zero-crossing in (f_left, f_mid]
      SearchRight  no zero-crossing in (f_left, f_mid]
                   (possible) zero-crossing in (f_mid, f_right]
 *)
let check_interval calc_zc f_left f_mid =
  let check i r x0 x1 =
    let rv = calc_zc x0 x1 in
    let r' = if rv = 0 then SearchRight
             else if x1 = 0.0 then FoundMid
             else SearchLeft in
    resolve_intervals r r' in
  fold_zxzx check SearchRight f_left f_mid

let printf = Printf.printf

let find ({ g = g; rightf_valid = rightf_valid;
            bothf_valid = bothf_valid;
            f0 = f0; t0 = t0; f1 = f1; t1 = t1;
            fta = fta; ftb = ftb; roots = roots;
            calc_zc = calc_zc } as s) dky c =
  let ttol = 100.0 *. epsilon_float *. max (abs_float t0) (abs_float t1) in

  (* A small optimisation to avoid copying or overwriting f1 *)
  let get_f_right ofr        = match ofr with None -> f1  | Some f -> f in
  let f_mid_from_f_right ofr = match ofr with None -> ftb | Some f -> f in

  (* update roots and c; return (t, f0_valid, f0, fta, ftb) *)
  let interval_too_small t_right f_left f_mid f_right' =
    if !debug then printf "z| too small at %.24e (< %.24e)\n" t_right ttol;
    dky t_right 0 c;      (* c = dky_0(t_right); update state *)
    ignore (update_roots calc_zc f_left (get_f_right f_right') roots);

    match f_right' with
    | None         -> (t_right, false, f_left,  f_mid, ftb)
    | Some f_right -> (t_right, true,  f_right, f_mid, f_left) in

  (* Searches between (t_left, f_left) and (t_right, f_right) to find the
     leftmost (t_mid, f_mid):
    
          | 
          |                                      f_right
          |
          |                  f_mid
          +--[t_left---------t_mid---------------t_right]--
          |
          |   f_left
          |

     t_left and t_right are the times that bound the interval
     f_left and f_right are the values at the end points

     f_mid is an array to be filled within the function (if necessary)
     f_right' is used in the optimisation to avoid copying or overwriting f1

     alpha is a parameter of the Illinois method, and
     i is used in its calculation

     seek() returns either:
       (t, false, f0', fta', ftb') - root found at original f_right
                                     (i.e., t = original t_right)
     or
       (t, true,  f0', fta', ftb') - root found at f0' (i.e., t < t_right)
   *)
  let rec seek (t_left, f_left, f_mid, t_right, f_right', alpha, i) =
    let dt = t_right -. t_left in
    let f_right = get_f_right f_right' in

    let leftmost_midpoint default =
      let check _ t_min x_left x_right =
        if x_left = 0.0 then t_min (* ignore expressions equal to zero at LHS *)
        else
          let sn   = (x_right /. alpha) /. x_left in
          let sn_d = 1.0 -. sn in
          (* refer Dahlquist and Bjorck, sec. 6.2.2
             stop if sn_d is not "large enough" *)
          let t' =
            if sn_d <= ttol then t_left +. (dt /. 2.0)
            else t_right +. (sn /. sn_d) *. dt in
          min t_min t' in
      fold_zxzx check default f_left f_right in

    if dt <= ttol
    then interval_too_small t_right f_left f_mid f_right'
    else
      let t_mid = leftmost_midpoint t_right in
      if t_mid = t_right
      then interval_too_small t_right f_left f_mid f_right'
      else begin

        dky t_mid 0 c;   (* c = dky_0(t_mid);    interpolate state *)
        g t_mid c f_mid; (* f_mid = g(t_mid, c); compute zc expressions *)

        match check_interval calc_zc f_left f_mid with
        | SearchLeft  ->
            if !debug then printf "z| (%.24e -- %.24e]   %.24e\n"
                           t_left t_mid t_right;
            let alpha = if i >= 1 then alpha *. 0.5 else alpha in
            let n_mid = f_mid_from_f_right f_right' in
            seek (t_left, f_left, n_mid,  t_mid,   Some f_mid, alpha, i + 1)

        | SearchRight ->
            if !debug then printf "z|  %.24e   (%.24e -- %.24e]\n"
                           t_left t_mid t_right;
            let alpha = if i >= 1 then alpha *. 2.0 else alpha in
            seek (t_mid,  f_mid,  f_left, t_right, f_right',   alpha, i + 1)

        | FoundMid    ->
            if !debug then printf "z|  %.24e   [%.24e]   %.24e\n"
                           t_left t_mid t_right;
            ignore (update_roots calc_zc f_left f_mid roots);
            let f_tmp = f_mid_from_f_right f_right' in
            (t_mid, true, f_mid, f_left, f_tmp)
      end
  in

  if not rightf_valid then init_mesh s c;

  if not bothf_valid then (clear_roots roots; None)
  else begin
    if !debug then
      (printf "z|\nz|---------- find(%.24e, %.24e)----------\n" t0 t1;
       log_limits f0 f1);

    match check_interval calc_zc f0 f1 with
    | SearchRight -> begin
        clear_roots roots;
        s.bothf_valid <- false;
        None
      end

    | FoundMid    -> begin
        if !debug then printf "z| zero-crossing at limit (%.24e)\n" t1;
        ignore (update_roots calc_zc f0 f1 roots);
        s.bothf_valid <- false;
        Some t1
      end

    | SearchLeft  -> begin
        let (t, v, f0', fta', ftb') =
          seek (t0, f0, fta, t1, None, 1.0, 0) in
        
        s.t0  <- t;
        s.f0  <- f0';
        s.bothf_valid <- v;
        s.fta <- fta';
        s.ftb <- ftb';

        Some t
      end
    end

let roots { roots } = roots

let set_root_directions s rd = (s.calc_zc <- get_check_root rd)

