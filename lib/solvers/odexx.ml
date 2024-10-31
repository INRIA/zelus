
open Zls

module type BUTCHER_TABLEAU =
sig (* {{{ *)

  val order : int     (* solver order *)

  val initial_reduction_limit_factor : float
  (* factor limiting the reduction of h after a failed step *)

  (* Butcher Tableau:

       a(0) |
       a(1) | b(1)
       a(2) | b(2)  b(3)
       a(3) | b(4)  b(5)  b(6)
       ...  |       ...
     -------+--------------
       a(n) | b(~)  b(~)  b(~) ...
            | b(+)  b(+)  b(+) ...

      The b(~) values must be included in b.
      The b(+) values are given indirectly via e.

      e/h = y_n+1 - y*_n+1 = b(~)s - b(+)s

  *)

  val a : float array   (* h coefficients; one per stage *)
  val b : float array   (* previous stage coefficients   *)
  val e : float array   (* error estimation coefficients *)
  val bi : float array  (* interpolation coefficients    *)

  (* let ns be the number of stages, then:
       size(a)  = ns x 1
       size(b)  = ns x ns
                  (but only the lower strictly triangular entries)
       size(e)  = ns
       size(bi) = ns x po 
                  (where po is the order of the interpolating polynomial)
   *)
     

end (* }}} *)

module GenericODE (Butcher : BUTCHER_TABLEAU) : STATE_SOLVER =
struct (* {{{1 *)
  open Bigarray

  let debug = ref false

  let pow = 1.0 /. float(Butcher.order)

  let mA r = Butcher.a.(r)
  let h_matB = Array.copy Butcher.b
  let update_mhB h = for i = 0 to Array.length h_matB - 1 do
      h_matB.(i) <- Butcher.b.(i) *. h
    done
  let mhB r c = if c >= r then 0.0 else h_matB.(((r-1)*r)/2 + c)
  let mhB_row r = Array.sub h_matB (((r-1)*r)/2) r

  let mE c = Butcher.e.(c)

  let maxK = Array.length(Butcher.a) - 1

  let rowsBI = Array.length(Butcher.a)
  let colsBI = Array.length(Butcher.bi) / rowsBI
  let maxBI  = colsBI - 1

  let h_matBI = Array.copy Butcher.bi
  let update_mhBI h = for i = 0 to Array.length h_matBI - 1 do
      h_matBI.(i) <- Butcher.bi.(i) *. h
    done
  let mhBI_row r = Array.sub h_matBI (r * colsBI) colsBI

  let minmax minimum maximum x = min maximum (max minimum x)

  let mapinto r f =
    for i = 0 to Array1.dim r - 1 do
      r.{i} <- f i
    done

  let fold2 f a v1 v2 =
    let acc = ref a in
    for i = 0 to min (length v1) (length v2) - 1 do
      acc := f !acc (get v1 i) (get v2 i)
    done;
    !acc

  let maxnorm2 f = fold2 (fun acc v1 v2 -> max acc (abs_float (f v1 v2))) 0.0

  type rhsfn = float -> Zls.carray -> Zls.carray -> unit
  type dkyfn = Zls.carray -> float -> int -> unit

  (* dx = sysf(t, y) describes the system dynamics

     y/time         is the current  mesh point
     yold/last_time is the previous mesh point
                    (and also used for intermediate values during the
                     calculation of the next mesh point)

     (y and yold are mutable because they are swapped after having calculated
      the next mesh point yold)

     h is the step size to be used for calculating the next mesh point.

     k.(0)    is the instantaneous derivative at the previous mesh point
     k.(maxK) is the instantaneous derivative at the current mesh point

     k.(1--maxK-1) track intermediate instantaneous derivatives during the
     calculation of the next mesh point.
  *)
  type t = {
    sysf : float -> Zls.carray -> Zls.carray -> unit;
    mutable y : Zls.carray;
    mutable time      : float;
    mutable last_time : float;
    mutable h         : float;
    mutable hmax      : float;

    k                 : Zls.carray array;

    mutable yold      : Zls.carray;

    (* -- parameters -- *)
    mutable stop_time  : float;

    (* bounds on small step sizes (mesh-points) *)
    mutable min_step   : float;
    mutable max_step   : float;

    (* initial/fixed step size *)
    mutable initial_step_size  : float option;

    mutable rel_tol    : float;
    mutable abs_tol    : float;
  }

  type nvec = Zls.carray
  let cmake = Array1.create float64 c_layout
  let unvec x = x

  let calculate_hmax tfinal max_step =
    if tfinal = infinity then max_step
    else if max_step = infinity then 0.1 *. tfinal
    else min max_step tfinal

  (* NB: y must be the initial state vector (y_0)
   *     k(0) must be the initial deriviatives vector (dy_0) *)
  let initial_stepsize { initial_step_size; abs_tol; rel_tol; max_step;
                         time; y; hmax; k } =
    let hmin = 16.0 *. epsilon_float *. abs_float time in
    match initial_step_size with
    | Some h -> minmax hmin max_step h
    | None   ->
      let threshold = abs_tol /. rel_tol in
      let rh =
        maxnorm2 (fun y dy -> dy /. (max (abs_float y) threshold)) y k.(0)
        /. (0.8 *. rel_tol ** pow)
      in
      max hmin (if hmax *. rh > 1.0 then 1.0 /. rh else hmax)

  let reinitialize ({ stop_time; max_step; sysf } as s) t ny =
    Bigarray.Array1.blit ny s.y;
    s.time      <- t;
    s.last_time <- t;
    s.hmax      <- calculate_hmax stop_time max_step;
    sysf t s.y s.k.(maxK); (* update initial derivatives;
                                            to be FSAL swapped into k.(0) *)
    s.h         <- initial_stepsize s

  let initialize f ydata =
    let y_len = Bigarray.Array1.dim ydata in
    let s = {
        sysf       = f;
        y          = Zls.cmake y_len;
        time       = 0.0;
        last_time  = 0.0;
        h          = 0.0;
        hmax       = 0.0;

        k          = Array.init (maxK + 1) (fun _ -> Zls.cmake y_len);
        yold       = Zls.cmake y_len;

        (* parameters *)
        stop_time = infinity;

        min_step          = 16.0 *. epsilon_float;
        max_step          = infinity;
        initial_step_size = None;

        rel_tol   = 1.0e-3;
        abs_tol   = 1.0e-6;
      } in
    Bigarray.Array1.blit ydata s.k.(0);
    reinitialize s 0.0 ydata;
    s

  let set_stop_time t v =
    if (v <= 0.0) then failwith "The stop time must be strictly positive.";
    t.stop_time <- v

  let set_min_step   t v = t.min_step <- v
  let set_max_step   t v = t.max_step <- v

  let set_tolerances t rel abs =
    if (rel <= 0.0 || abs <= 0.0)
    then failwith "Tolerance values must be strictly positive.";
    (t.rel_tol <- rel; t.abs_tol <- abs)

  let make_newval y k s =
    let hB = mhB_row s in
    let newval i =
      let acc = ref y.{i} in
      for si = 0 to s - 1 do
        acc := !acc +. k.(si).{i} *. hB.(si)
      done;
      !acc in
    newval

  let calculate_error threshold k y ynew =
    let maxerr = ref 0.0 in
    for i = 0 to Bigarray.Array1.dim y - 1 do
      let kE = ref 0.0 in
      for s = 0 to maxK do
        kE := !kE +. k.(s).{i} *. mE s
      done;
      let err = !kE /. (max threshold (max (abs_float y.{i})
                                           (abs_float ynew.{i}))) in
      maxerr := max !maxerr (abs_float err)
    done;
    !maxerr

  let log_step t y dy t' y' dy' =
    Printf.printf
      "s|        % .24e                                       % .24e\n" t t';
    for i = 0 to Array1.dim y - 1 do
      Printf.printf "s| f[% 2d]: % .24e (% .24e) --> % .24e (% .24e)\n"
        i (y.{i}) dy.{i} y'.{i} dy'.{i}
    done

  (* TODO: add stats: nfevals, nfailed, nsteps *)
  let rec step s t_limit user_y =
    let { stop_time; min_step; abs_tol; rel_tol;
          sysf = f; time = t; h = h; hmax = hmax;
          k = k; y = y; yold = ynew; } = s in

    (* First Same As Last (FSAL) swap; doing it after the previous
       step invalidates the interpolation routine. *)
    let tmpK = k.(0) in
    k.(0) <- k.(maxK);
    k.(maxK) <- tmpK;

    let hmin = 16.0 *. epsilon_float *. abs_float t in
    let h = minmax hmin hmax h in
    let max_t = min t_limit stop_time in
    let h, finished =
      if 1.1 *. h >= abs_float (max_t -. t)
      then (max_t -. t, true)
      else (h, false) in

    if h < s.min_step then failwith
        (Printf.sprintf
           "odexx: step size < min step size (\n       now=%.24e\n         h=%.24e\n< min_step=%.24e)"
           t h s.min_step);

    if !debug then Printf.printf "s|\ns|----------step(%.24e)----------\n" max_t;

    let rec onestep alreadyfailed h =

      (* approximate next state vector *)
      update_mhB h;
      for s = 1 to maxK - 1 do
        mapinto ynew (make_newval y k s);
        f (t +. h *. mA s) ynew k.(s)
      done;

      let tnew = if finished then max_t else t +. h *. (mA maxK) in
      mapinto ynew (make_newval y k maxK);
      f tnew ynew k.(maxK);
      if !debug then log_step t y k.(0) tnew ynew k.(maxK);

      let err = h *. calculate_error (abs_tol /. rel_tol) k y ynew in
      if err > rel_tol then begin
        if !debug then Printf.printf "s| error exceeds tolerance\n";

        if h <= hmin then failwith
            (Printf.sprintf "Error (%e) > relative tolerance (%e) at t=%e"
               err rel_tol t);

        let nexth =
          if alreadyfailed then max hmin (0.5 *. h)
          else max hmin (h *. max Butcher.initial_reduction_limit_factor
                             (0.8 *.  (rel_tol /. err) ** pow)) in
        onestep true nexth
      end
      else
        let h = tnew -. t in
        let nexth =
          if alreadyfailed then h
          else let f = 1.25 *. (err /. rel_tol) ** pow in
            if f > 0.2 then h /. f else 5.0 *. h in
        (tnew, nexth)
    in
    let nextt, nexth = onestep false h in

    (* advance a step *)
    s.y  <- ynew;
    s.yold <- y;

    Bigarray.Array1.blit ynew user_y;
    s.last_time <- t;
    s.time <- nextt;
    s.h <- nexth;
    s.time

  let get_dky { last_time = t; time = t'; h = h; yold = y; k = k }
      yi ti kd =

    if kd > 0 then
      failwith "get_dky: requested derivative cannot be interpolated";
    if ti < t || ti > t' then
      failwith "get_dky: requested time is out of range";

    let h  = t' -. t        in
    let th = (ti -. t) /. h in

    update_mhBI h;
    for i = 0 to Bigarray.Array1.dim y - 1 do
      let ya = ref y.{i} in
      for s = 0 to maxK do
        let k = k.(s).{i} in
        let hbi = mhBI_row s in
        let acc = ref 0.0 in
        for j = maxBI downto 0 do
          acc := (!acc +. k *. hbi.(j)) *. th
        done;
        ya := !ya +. !acc
      done;
      yi.{i} <- !ya
    done

end (* }}} *)

module Ode23 = GenericODE (
  struct
  let order = 3
  let initial_reduction_limit_factor = 0.5

  let a = [| 0.0; 1.0/.2.0; 3.0/.4.0; 1.0 |]

  let b = [| 1.0/.2.0;
               0.0;    3.0/.4.0;
             2.0/.9.0; 1.0/.3.0; 4.0/.9.0 |]

  let e = [| -5.0/.72.0; 1.0/.12.0; 1.0/.9.0; -1.0/.8.0 |]

  let bi = [| 1.0; -4.0/.3.0;  5.0/.9.0;
              0.0;    1.0;    -2.0/.3.0;
              0.0;  4.0/.3.0; -8.0/.9.0;
              0.0;   -1.0;       1.0      |]
  end)

module Ode45 = GenericODE (
  struct
  let order = 5
  let initial_reduction_limit_factor = 0.1

  let a = [| 0.0; 1.0/.5.0; 3.0/.10.0; 4.0/.5.0; 8.0/.9.0; 1.0; 1.0 |]

  let b = [|
        1.0/. 5.0;
        3.0/.40.0;        9.0/.40.0;
       44.0/.45.0;      -56.0/.15.0;      32.0/.9.0;
    19372.0/.6561.0; -25360.0/.2187.0; 64448.0/.6561.0; -212.0/.729.0;
     9017.0/.3168.0;   -355.0/.33.0;   46732.0/.5247.0;   49.0/.176.0; -5103.0/.18656.0;
       35.0/.384.0;         0.0;         500.0/.1113.0;  125.0/.192.0; -2187.0/.6784.0; 11.0/.84.0;
          |]

  let e = [|     71.0/.57600.0;      0.0;     -71.0/.16695.0; 71.0/.1920.0;
             -17253.0/.339200.0; 22.0/.525.0;  -1.0/.40.0  |]

  let bi = [| 1.0;  -183.0/.64.0;      37.0/.12.0;    -145.0/.128.0;
              0.0;       0.0;             0.0;             0.0;
              0.0;  1500.0/.371.0;  -1000.0/.159.0;   1000.0/.371.0;
              0.0;  -125.0/.32.0;     125.0/.12.0;    -375.0/.64.0;
              0.0;  9477.0/.3392.0;  -729.0/.106.0;  25515.0/.6784.0;
              0.0;   -11.0/.7.0;       11.0/.3.0;      -55.0/.28.0;
              0.0;     3.0/.2.0;         -4.0;           5.0/.2.0     |]
  end)

