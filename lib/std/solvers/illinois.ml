let debug = ref false
		
let printf x = Format.printf x

type root_direction = Up | Down | Either | Ignore

let extra_precision = ref false
let set_precise_logging _ = (extra_precision := true)

let fold_zxzx f acc f0 f1 =
  let n = Zls.length f0 in
  let rec fold acc i =
    if i = n then acc
    else
      let acc' = f i acc f0.{i} f1.{i} in
      fold acc' (i + 1)
  in fold acc 0

(* return a function that looks for zero-crossings *)
let get_check_root rdir =
  let check_up     x0 x1 = if x0 < 0.0 && x1 >= 0.0 then  1l else 0l in
  let check_down   x0 x1 = if x0 > 0.0 && x1 <= 0.0 then -1l else 0l in
  let check_either x0 x1 = if x0 < 0.0 && x1 >= 0.0 then  1l else
                           if x0 > 0.0 && x1 <= 0.0 then -1l else 0l in
  let no_check x0 x1 = 0l in

  match rdir with
  | Up     -> check_up
  | Down   -> check_down
  | Either -> check_either
  | Ignore -> no_check

(* returns true if a signal has moved from zero to a stritly positive value *)
let takeoff f0 f1 =
  let n = Zls.length f0 in
  let rec fold acc i =
    if i = n then acc
    else if acc then acc else fold ((f0.{i} = 0.0) && (f1.{i} > 0.0)) (i + 1)
  in fold false 0
	
(* return a function that looks for zero-crossings between f0 and f1 *)
let make_check_root rdir f0 f1 =
  let check = get_check_root rdir in
  (fun i -> check f0.{i} f1.{i})

let update_roots calc_zc f0 f1 roots =
  let update i found x0 x1 =
    let zc = calc_zc x0 x1 in
    roots.{i} <- zc;
    found || (zc <> 0l)
  in
  fold_zxzx update false f0 f1

let clear_roots roots =
  for i = 0 to Zls.length roots - 1 do
    roots.{i} <- 0l
  done

let log_limits f0 f1 =
  let logf i _ = printf "z| g[% 2d]: % .24e --> % .24e@." i in
  fold_zxzx logf () f0 f1

let log_limit f0 =
  let logf i _ x _ = printf "z| g[% 2d]: % .24e@." i x in
  fold_zxzx logf () f0 f0

type zcfn  = float -> Zls.carray -> Zls.carray -> unit

(* type of a session with the solver *)
(*  zx = g(t, c) yields the values of system zero-crossing expressions
    
    f0/t0 are the zero-crossing expression values at the last mesh point
    f1/t1 are the zero-crossing expression values at the next mesh point

    bothf_valid is true when both f0/t0 and f1/t1 are valid and thus find
    can check for zero-crossings between them.

    roots is the array of booleans returned to callers to indicate on which
    expressions zero-crossings have been detected.

    calc_zc determines the kind of zero-crossings to seek and report.

    fta and ftb are temporary arrays used when searching for zero-crossings.
    They are kept in the session as an optimisation to avoid having to
    continually create and destroy arrays.
 *)
type t = {
    g : zcfn;
    mutable bothf_valid  : bool;

    mutable f0 : Zls.carray;
    mutable t0 : float;

    mutable f1 : Zls.carray;
    mutable t1 : float;

    mutable calc_zc : float -> float -> int32;

    mutable fta : Zls.carray;
    mutable ftb : Zls.carray;
  }

(* Called from find when bothf_valid = false to initialise f1. *)
let reinitialize ({ g; f1 = f1; t1 = t1 } as s) t c =
  s.t1 <- t;
  g t1 c f1;   (* fill f1, because it is immediately copied into f0 by next_mesh *)
  if !debug then (printf "z|---------- init(%.24e, ... ----------@." t;
                  log_limit s.f1);
  s.bothf_valid  <- false

let initialize_only nroots g c =
  {
    g = g;
    bothf_valid  = false;
    
    f0 = Zls.cmake nroots;
    t0 = 0.0;
    
    f1 = Zls.cmake nroots;
    t1 = 0.0;
    
    fta = Zls.cmake nroots;
    ftb = Zls.cmake nroots;
    
    calc_zc = get_check_root Up;
  }

let initialize nroots g c =
  let s = initialize_only nroots g c in
  reinitialize s 0.0 c;
  s


let num_roots { f0 } = Zls.length f0

(* f0/t0 take the previous values of f1/t1, f1/t1 are refreshed by g *)
let step ({ g; f0 = f0; f1 = f1; t1 = t1 } as s) t c =
  (* swap f0 and f1; f0 takes the previous value of f1 *)
  s.f0 <- f1;
  s.t0 <- t1;
  s.f1 <- f0;
  s.t1 <- t;

  (* calculate a new value for f1 *)
  g t c s.f1;
  s.bothf_valid <- true;

  if !debug then
    (printf "z|---------- step(%.24e, %.24e)----------@." s.t0 s.t1;
     log_limits s.f0 s.f1)

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
    let r' = if rv = 0l then SearchRight
             else if x1 = 0.0 then FoundMid
             else SearchLeft in
    resolve_intervals r r' in
  fold_zxzx check SearchRight f_left f_mid

(* locates the zero-crossing *)
let find ({ g = g; bothf_valid = bothf_valid;
            f0 = f0; t0 = t0; f1 = f1; t1 = t1;
            fta = fta; ftb = ftb; calc_zc = calc_zc } as s) (dky, c) roots =
  let ttol = 100.0 *. epsilon_float *. max (abs_float t0) (abs_float t1) in

  (* A small optimisation to avoid copying or overwriting f1 *)
  let get_f_right ofr        = match ofr with None -> f1  | Some f -> f in
  let f_mid_from_f_right ofr = match ofr with None -> ftb | Some f -> f in

  (* update roots and c; return (t, f0_valid, f0, fta, ftb) *)
  let interval_too_small t_left t_right f_left f_mid f_right' =
    dky t_right 0;      (* c = dky_0(t_right); update state *)
    ignore (update_roots calc_zc f_left (get_f_right f_right') roots);

    if !debug then
      (printf
          "z|---------- stall(%.24e, %.24e) {interval < %.24e !}--@."
          t_left t_right ttol;
       log_limits f_left (get_f_right f_right'));

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
    then interval_too_small t_left t_right f_left f_mid f_right'
    else
      let t_mid = leftmost_midpoint t_right in
      if t_mid = t_right
      then interval_too_small t_left t_right f_left f_mid f_right'
      else begin

        dky t_mid 0;     (* c = dky_0(t_mid);    interpolate state *)
        g t_mid c f_mid; (* f_mid = g(t_mid, c); compute zc expressions *)

        match check_interval calc_zc f_left f_mid with
        | SearchLeft  ->
            if !debug then printf "z| (%.24e -- %.24e]   %.24e@."
                           t_left t_mid t_right;
            let alpha = if i >= 1 then alpha *. 0.5 else alpha in
            let n_mid = f_mid_from_f_right f_right' in
            seek (t_left, f_left, n_mid,  t_mid,   Some f_mid, alpha, i + 1)

        | SearchRight ->
            if !debug then printf "z|  %.24e   (%.24e -- %.24e]@."
                           t_left t_mid t_right;
            let alpha = if i >= 1 then alpha *. 2.0 else alpha in
            seek (t_mid,  f_mid,  f_left, t_right, f_right',   alpha, i + 1)

        | FoundMid    ->
            if !debug then printf "z|  %.24e   [%.24e]   %.24e@."
                           t_left t_mid t_right;
            ignore (update_roots calc_zc f_left f_mid roots);
            let f_tmp = f_mid_from_f_right f_right' in
            (t_mid, true, f_mid, f_left, f_tmp)
      end
  in

  if not bothf_valid then (clear_roots roots; assert false)
  else begin
    if !debug then
      printf "z|\nz|---------- find(%.24e, %.24e)----------@." t0 t1;

    match check_interval calc_zc f0 f1 with
    | SearchRight -> begin
        clear_roots roots;
        s.bothf_valid <- false;
        assert false
      end

    | FoundMid    -> begin
        if !debug then printf "z| zero-crossing at limit (%.24e)@." t1;
        ignore (update_roots calc_zc f0 f1 roots);
        s.bothf_valid <- false;
        t1
      end

    | SearchLeft  -> begin
        let (t, v, f0', fta', ftb') =
          seek (t0, f0, fta, t1, None, 1.0, 0) in
        
        s.t0  <- t;
        s.f0  <- f0';
        s.bothf_valid <- v;
        s.fta <- fta';
        s.ftb <- ftb';

        t
      end
    end

let takeoff { bothf_valid = bothf_valid; f0; f1 } =
  bothf_valid && (takeoff f0 f1)
								
let has_roots { bothf_valid = bothf_valid; t0; f0; t1; f1; calc_zc = calc_zc }
  = bothf_valid && (check_interval calc_zc f0 f1 <> SearchRight)
		    
let set_root_directions s rd = (s.calc_zc <- get_check_root rd)

