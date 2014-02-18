
(* TODO: test solvers:
      RK-4 with custom Illinois
 *)

open Solvers

module RungeKutta4 : STATE_SOLVER =
  struct (* {{{1 *)
    include SolverInfrastructure

    (* dx = sysf(t, y) describes the system dynamics
      
       y/time       is the current  mesh point
       y1/last_time is the previous mesh point
                    (and also used for intermediate values during the
                    calculation of the next mesh point)

       (y and y1 are mutable because they are swapped after having calculated
        the next mesh point in y1)

       h is the step size to be used for calculating the next mesh point.

       k1 is the instantaneous derivative at the previous mesh point
       k4 is the instantaneous derivative at the current mesh point

       k1, k2, k3, k4 track intermediate instantaneous derivatives during the
       calculation of the next mesh point.

       y2 stores values for the current mesh point calculated at a higher order
       and used solely as a measure of approximation error.
     *)
    type solver_t = {
        sysf : float -> cvec -> cvec -> unit;
        mutable y : cvec;
        mutable time      : float;
        mutable last_time : float;
        mutable h         : float;
	k                 : cvec array;
        mutable y1        : cvec;
      }
    type t = solver_t parameter_t

    let init f ydata =
      let y_len = length ydata in
      let p = init_parameters ({
                sysf       = f;
                y          = create y_len;
                time       = 0.0;
                last_time  = 0.0;
                h          = 1.0;
		k          = Array.make 4 (create y_len);
                y1         = create y_len;
              }) in
      copy ydata p.solver.y;
      p.solver.h <- p.step_size;
      p

    let butcher_c = [|0.0; 0.5; 0.5; 1.0|]
    let butcher_b = [|1.0/.6.0; 1.0/.3.0; 1.0/.3.0; 1.0/.6.0|]
    let butcher_a = [|
      [|0.5; 0.0; 0.0|];
      [|0.0; 0.5; 0.0|];
      [|0.0; 0.0; 1.0|];
    |]

    let reinit s t ny =
      copy ny s.solver.y;
      s.solver.time      <- t;
      s.solver.last_time <- t;
      s.solver.h         <- s.step_size

    let mapinto r f =
      for i = 0 to (length r - 1) do
        set r i (f i)
      done

    let rec step s time_limit user_y =
      let { stop_time; min_step; abs_tol;
            solver = { sysf = f; y; time = t; h = h; k = k;
                       y1 = y1 }; } = s in
      let max_t = min time_limit stop_time in
      let h = min s.max_step (max_t -. t) in
      if h < s.min_step then failwith
        (Printf.sprintf
          "rk4: step to limit < min step (\n  limit=%.24e\n    now=%.24e\n    min=%.24e)"
          t max_t s.min_step);

      if !debug then printf "s|\ns|----------step(%.24e)----------\n" max_t;


      (* k1 = f(t, y) *)
      f (t +. h *. butcher_c.(0)) y k.(0);

      for step=1 to 3 do
	mapinto y1 (fun i -> get y i +. (h *. butcher_a.(step-1).(0) *. get k.(0) i)
	                           +. (h *. butcher_a.(step-1).(1) *. get k.(1) i)
                                   +. (h *. butcher_a.(step-1).(2) *. get k.(2) i));
	f (t +. h *. butcher_c.(step)) y1 k.(step);
      done;

      (* y1 = y + (h/6)*(k1 + 2k2 + 2k3 + k4)   *)
      mapinto y1 (fun i -> get y i);
      for step=0 to 3 do
	mapinto y1 (fun i -> get y1 i +. (h *. butcher_b.(step) *. get k.(step) i));
      done;

      if !debug then log_step t y k.(0) (t +. h) y1 k.(3);

          (* swap y and y1 *)
          s.solver.y  <- y1;
          s.solver.y1 <- y;

          copy y1 user_y;
          s.solver.last_time <- t;
          s.solver.time <- t +. h;
          s.solver.time

    let full_step = make_full_step step

    (* Cubic Hermite Interpolation *)
    let get_dky { solver = { last_time = x0; y1 = f0; k = k_runge; (* conflict with "k" ! *)(*k1 = f'0;*)
                             time      = x1; y  = f1; (*k4 = f'1*) } } t k y =
      if k > 0 then
        failwith "get_dky: requested derivative cannot be interpolated";
      if t < x0 || t > x1 then
        failwith "get_dky: requested time is out of range";

      let h        = x1 -. x0         in
      let th       = (t -. x0) /. h   in
      let m_th     = 1.0 -. th        in

      let px f0 f1 f'0 f'1 =
        let delta_f0 = f1 -. f0 in
        m_th *. f0  +.  th *. f1
          +. th *. m_th *. (m_th *. (h *. f'0  -.  delta_f0)
                            -.  th *. (h *. f'1  -.  delta_f0))
      in
      for i = 0 to (length f0 - 1) do
        set y i (px (get f0 i) (get f1 i) (get  k_runge.(0) i) (get  k_runge.(3) i))
      done

  end (* }}} *)

let _ =
  Fixedstep.register
    "rk4butcherF"
    "internal solver: fixed-step Runge-Kutta 4 method (with butcher-tableau way of computation"
    (module RungeKutta4 : STATE_SOLVER)

