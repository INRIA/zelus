 
(* Compare two floats for equality, see:
 * http://www.cygnus-software.com/papers/comparingfloats/comparingfloats.htm *)
let time_eq f1 f2 =
  if abs_float (f1 -. f2) < min_float
  then true (* absolute error check for numbers around to zero *)
  else
    let rel_error =
      if abs_float f1 > abs_float f2
      then abs_float ((f1 -. f2) /. f1)
      else abs_float ((f1 -. f2) /. f2)
    in
    (rel_error <= 0.000001)
    (* Compare times with 99.9999% accuracy. *)

let time_leq t1 t2 = t1 < t2 || time_eq t1 t2
let time_geq t1 t2 = t1 > t2 || time_eq t1 t2

module type SOLVER =
  sig (* {{{ *)

    (* type of a session with the solver *)
    type t
    type root_direction = Up | Down | Either | Ignore
    type sim_result = Roots | Continue | Stop

    exception Solvererror of string

    type cvec
    val cvec_create : int -> cvec
    val cvec_get    : cvec -> int -> float
    val cvec_set    : cvec -> int -> float -> unit
    val cvec_log    : string -> float -> cvec -> unit
    val cvec_copy   : cvec -> cvec -> unit

    type zvec
    val zvec_get    : zvec -> int -> bool
    val zvec_log    : string -> float -> zvec -> unit

    type zxvec
    val zxvec_set   : zxvec -> int -> float -> unit
    val zxvec_log   : string -> float -> zxvec -> unit

    (* [(no_roots_in, no_roots_out) = ignore_roots nroots] returns two vectors,
       each with [nroots] elements: [no_roots_in] is a vector where all roots
       are false, [no_roots_out] is an empty vector. *)
    val ignore_roots  : int -> zvec * zxvec

    (* generic solver parameters *)
    val set_stop_time       : t -> float -> unit
    val set_min_step        : t -> float -> unit
    val set_max_step        : t -> float -> unit
    val set_tolerances      : t -> float -> float -> unit
                             (* relative -> absolute *)
    val set_root_directions : t -> root_direction -> unit

    (* always advance the time horizon by the given increment, regardless of the
       horizon requested. *)
    val set_horizon_step    : t -> float -> unit

    (* log floats with more precision *)
    val set_precise_logging : t -> unit

    (* Given the number of continuous states in the system being simulated, return a
     * list that can be passed to Arg.parse to allow simulation parameters to be set
     * at the command line. *)
    val args : int -> (Arg.key * Arg.spec * Arg.doc) list
    
    (* [init f (nroots, g) c] creates a session from a function [f], that
       calculates instantaneous derivatives, a function [g] that calculates
       [nroots] zero-crossing expression values, and an initial state vector
       [c]. *)
    val init : (float -> cvec -> cvec -> unit) ->
               int * (float -> cvec -> zxvec -> unit) ->
               cvec ->
               t

    (* [reinit s t c] reinitializes the solver with the given time [t] and
       vector of continuous states [c]. *)
    val reinit : t -> float -> cvec -> unit 

    (* [(t', r) = step s tl c] given a state vector [c], takes a step to the
       next detected zero-crossing, or the given time limit [tl]. The time
       reached is given by [t'] and [r] indicates whether a zero-crossing was
       found [r = Roots], whether the stop time was reached [r = Stop], or
       otherwise [r = Continue]. *)
    val go : t -> float -> cvec -> float * sim_result

   (* [roots s] returns a zvec filled with information about the roots detected
      by [find]. Note: the same zvec will be overwritten by a subsequent call to
      [roots] with the same session [s]. *)
    val roots : t -> zvec

  end (* }}} *)

module type STATE_SOLVER =
  sig (* {{{ *)
    (* vector of continuous states / instantaneous derivatives *)
    type cvec

    val create : int -> cvec
    val get    : cvec -> int -> float
    val set    : cvec -> int -> float -> unit
    val log    : string -> float -> cvec -> unit
    val copy   : cvec -> cvec -> unit

    (* Given the number of continuous states in the system being simulated, return a
     * list that can be passed to Arg.parse to allow simulation parameters to be set
     * at the command line. *)
    val args : int -> (Arg.key * Arg.spec * Arg.doc) list

    (* type of a session with the solver *)
    type t

    exception Solvererror of string

    (* [init f c] creates a solver session from a function [f] and an initial
       state vector [c].  *)
    val init : (float -> cvec -> cvec -> unit) -> cvec -> t

    (* [reinit s t c] reinitializes the solver with the given time [t] and
       vector of continuous states [c]. *)
    val reinit : t -> float -> cvec -> unit

    (* generic solver parameters *)
    val set_stop_time  : t -> float -> unit
    val set_min_step   : t -> float -> unit
    val set_max_step   : t -> float -> unit
    val set_tolerances : t -> float -> float -> unit

    (* log floats with more precision *)
    val set_precise_logging : t -> unit

    (* [t' = step s tl c] given a state vector [c], takes a step to the next
       'mesh-point', or the given time limit [tl] (whichever is sooner). *)
    val step : t -> float -> cvec -> float

    (* [t' = full_step s tl c] given a state vector [c], takes a step to
       the given time limit [tl]. *)
    val full_step : t -> float -> cvec -> float

    (* [get_dky s t k c] for any time [t] since the last mesh-point, or initial
       instant, put [k]th derivatives into [c]. *)
    val get_dky : t -> float -> int -> cvec -> unit

  end (* }}} *)

module type ZEROC_SOLVER =
  sig (* {{{ *)

    type root_direction = Up | Down | Either | Ignore

    (* vector of zero-crossing results *)
    type zvec
    val zvec_get   : zvec -> int -> bool
    val zvec_set   : zvec -> int -> root_direction -> unit
    val zvec_log   : string -> float -> zvec -> unit

    (* vector of zero-crossing expressions *)
    type zxvec
    val zxvec_get : zxvec -> int -> float
    val zxvec_set : zxvec -> int -> float -> unit
    val zxvec_log : string -> float -> zxvec -> unit

    (* [(no_roots_in, no_roots_out) = ignore_roots nroots] returns two vectors,
       each with [nroots] elements: [no_roots_in] is a vector where all roots
       are false, [no_roots_out] is an empty vector. *)
    val ignore_roots : int -> zvec * zxvec

    (* A list that can be passed to Arg.parse to allow simulation
       parameters to be set at the command line. *)
    val args : (Arg.key * Arg.spec * Arg.doc) list

    (* type of a session with the solver *)
    type 'cvec t

    (* [init (nroots, g)] creates a solver session for [nroots] root
       expressions returned by the function [g]. *)
    val init : int * (float -> 'cvec -> zxvec -> unit) -> 'cvec -> 'cvec t

    (* Returns the number of roots managed by this solver. *)
    val num_roots : 'cvec t -> int

    (* log floats with more precision *)
    val set_precise_logging : 'cvec t -> unit

    val reinit : 'cvec t -> float -> 'cvec -> unit

    (* [next_mesh s t c] is called for a session [s] after a new mesh point has
       been calculated at [t] with values [c]. Values for [t] will never
       decrease between successive calls. *)
    val next_mesh : 'cvec t -> float -> 'cvec -> unit

    (* [find s dky c] locates the first zero-crossing between either the last
       two mesh-points, or, between the last zero-crossing that was returned
       and the last mesh-point; with priority to the latter. It takes a
       function [dky] that gives the nth derivative at any time between
       the last two mesh-points (most solvers will never request n beyond a
       fixed maximum). If a zero-crossing is found, then c is updated with
       the values of the continuous states at that instant. The internal notion
       of mesh-points is updated by calls to check. *)
    val find : 'cvec t ->
               (float -> int -> 'cvec -> unit) ->
               'cvec ->
               float option

   (* [roots s] returns a zvec filled with information about the roots detected
      by [find]. Note: the same zvec will be overwritten by a subsequent call to
      [roots] with the same session [s]. *)
    val roots : 'cvec t -> zvec

    val set_root_directions : 'cvec t -> root_direction -> unit

  end (* }}} *)

module type SOLVER_FUNCTOR =
  functor (State : STATE_SOLVER) ->
  functor (Zeroc : ZEROC_SOLVER) ->
  SOLVER

module Presolver (State : STATE_SOLVER) (Zeroc : ZEROC_SOLVER) =
  struct (* {{{ *)

    type t = {
        cs                  : State.t;
        zs                  : State.cvec Zeroc.t;
        mutable i_step      : int;
        mutable horizon_inc : float option;

        mutable stop_time   : float option;
        mutable last_time   : float;
      }
    type root_direction = Up | Down | Either | Ignore
    type sim_result = Roots | Continue | Stop

    exception Solvererror = State.Solvererror

    (* Ugly, but how to avoid? *)
    let to_zeroc_root v =
      match v with
      | Up     -> Zeroc.Up
      | Down   -> Zeroc.Down
      | Either -> Zeroc.Either
      | Ignore -> Zeroc.Ignore

    type cvec = State.cvec

    let cvec_create = State.create
    let cvec_get    = State.get
    let cvec_set    = State.set
    let cvec_log    = State.log
    let cvec_copy   = State.copy

    type zvec = Zeroc.zvec
    let zvec_get       = Zeroc.zvec_get
    let zvec_set v i d = Zeroc.zvec_set v i (to_zeroc_root d)
    let zvec_log       = Zeroc.zvec_log

    type zxvec = Zeroc.zxvec
    let zxvec_set    = Zeroc.zxvec_set
    let zxvec_log    = Zeroc.zxvec_log

    let ignore_roots = Zeroc.ignore_roots

    let set_stop_time ({cs} as s) v =
      s.stop_time <- Some v;
      State.set_stop_time cs v

    let set_min_step   {cs} v = State.set_min_step  cs v

    let set_max_step ({cs; horizon_inc} as s) v =
      (if horizon_inc <> None then s.horizon_inc <- Some v);
      State.set_max_step cs v

    let set_horizon_step ({cs; i_step} as s) v =
      if i_step <> 0 then
        raise (Solvererror "set_horizon_step cannot be called mid-simulation!");
      s.horizon_inc <- Some v;
      State.set_max_step cs v

    let set_tolerances {cs} rel abs = State.set_tolerances cs rel abs

    let set_root_directions {zs} d =
      Zeroc.set_root_directions zs (to_zeroc_root d)

    let set_precise_logging {cs; zs} =
      State.set_precise_logging cs;
      Zeroc.set_precise_logging zs

    let args n = State.args n @ Zeroc.args

    let init f gi c =
      let cs = State.init f c in
      let zs = Zeroc.init gi c in
      { cs = cs; zs = zs; i_step = 0; horizon_inc = None;
        stop_time = None; last_time = 0.0 }

    let reinit {cs; zs} t c =
      State.reinit cs t c;
      Zeroc.reinit zs t c

    let at_max_time { stop_time = stop; last_time = last } =
      match stop with
      | Some t -> time_geq last t
      | _ -> false

    let go ({cs; zs; i_step; horizon_inc; last_time} as s) t_hor c =
      let t_hor = match horizon_inc with
                  | None -> t_hor
                  | Some h -> float (i_step + 1) *. h in

      let rec step () =
        let t' = State.step cs t_hor c in
        s.i_step <- i_step + 1;
        Zeroc.next_mesh zs t' c;
        match Zeroc.find zs (State.get_dky cs) c with
        | None when time_geq t' t_hor ->
            (s.last_time <- t'; (t', Continue))
        | Some t ->
            (s.last_time <- t;  (t,  Roots))
        | None -> step ()
      in

      if at_max_time s then (last_time, Stop)
      else match Zeroc.find zs (State.get_dky cs) c with
           | None   -> step ()
           | Some t -> let () = s.last_time <- t in
                       (t, Roots)

    let roots {zs} = Zeroc.roots zs

  end (* }}} *)

module Solver = (Presolver : SOLVER_FUNCTOR)

(* Boilerplate common to many solvers *)

let printf = Printf.printf

module SolverInfrastructure =
  struct (* {{{ *)
    type cvec = (float, Bigarray.float64_elt, Bigarray.c_layout) Bigarray.Array1.t

    let create n =
      let r = Bigarray.Array1.create Bigarray.float64 Bigarray.c_layout n in
      (*Bigarray.Array1.fill r 0.0;*)
      r

    let get      = Bigarray.Array1.get
    let set      = Bigarray.Array1.set
    let copy     = Bigarray.Array1.blit
    let length   = Bigarray.Array1.dim

    let minmax minimum maximum x = min maximum (max minimum x)

    let app f v =
      for i = 0 to (length v - 1) do
        f i (get v i)
      done

    let mapinto r f =
      for i = 0 to (length r - 1) do
        set r i (f i)
      done

    let fold f a v =
      let acc = ref a in
      for i = 0 to length v - 1 do
        acc := f !acc (get v i)
      done;
      !acc

    let fold2 f a v1 v2 =
      let acc = ref a in
      for i = 0 to min (length v1) (length v2) - 1 do
        acc := f !acc (get v1 i) (get v2 i)
      done;
      !acc

    let maxnorm f = fold (fun acc v -> max acc (abs_float (f v))) 0.0
    let maxnorm2 f = fold2 (fun acc v1 v2 -> max acc (abs_float (f v1 v2))) 0.0

    let extra_precision = ref false
    let set_precise_logging _ = (extra_precision := true)

    let log l t c =
      let pr f =
        if !extra_precision
        then printf "\t% .15e"
        else printf "\t% e" in

      if !extra_precision
      then printf "%s%.15e" l t
      else printf "%s%e" l t;

      app pr c;
      printf "\n"

    let debug = ref false

    exception Solvererror of string
    let failwith s = raise (Solvererror s)

    let args n_eq = [
        ("-debugs", Arg.Set debug, " Log numerical approximation.")
      ]

    type 'a parameter_t = {
        mutable stop_time  : float;

        (* bounds on small step sizes (mesh-points) *)
        mutable min_step   : float;
        mutable max_step   : float;

        (* initial/fixed step size *)
        mutable initial_step_size  : float option;

        mutable rel_tol    : float;
        mutable abs_tol    : float;
        solver             : 'a;
      }

    let init_parameters s = {
        stop_time = infinity;

        min_step          = 16.0 *. epsilon_float;
        max_step          = infinity;
        initial_step_size = None;

        rel_tol   = 1.0e-3;
        abs_tol   = 1.0e-6;
        solver    = s;
      }

    let set_stop_time t v =
      if (v <= 0.0) then failwith "The stop time must be strictly positive.";
      t.stop_time <- v

    (* h is the step size of a fixed step solver *)
    let set_fixed_stop_time t h v =
      t.stop_time <- floor (v /. h) *. h

    let set_min_step   t v = t.min_step <- v
    let set_max_step   t v = t.max_step <- v

    let set_tolerances t rel abs =
      if (rel <= 0.0 || abs <= 0.0)
      then failwith "Tolerance values must be strictly positive.";
      (t.rel_tol <- rel; t.abs_tol <- abs)

    let log_step t y dy t' y' dy' =
      let pr i yi =
        printf "s| f[% 2d]: % .24e (% .24e) --> % .24e (% .24e)\n"
          i yi (get dy i) (get y' i) (get dy' i) in
      printf "s|        % .24e                                       % .24e\n"
             t t';
      app pr y

    let make_full_step step =
      let full_step ({ stop_time = stop_time } as s) time_l c =
        let tl = min stop_time time_l in
        let rec fs () =
          let t' = step s tl c in
          if time_geq tl t' then t' else fs () in
        fs ()
      in
      full_step

    (*
      To complete the implementation, add:
     
      type t
      val init : (float -> cvec -> cvec -> unit) -> cvec -> t
      val reinit : t -> float -> cvec -> unit
      val step : t -> float -> cvec -> float
      val full_step : t -> float -> cvec -> float
      val get_dky : t -> float -> int -> cvec -> unit
    *)

  end (* }}} *)

module ZerosInfrastructure =
  struct (* {{{ *)

    type root_direction = Up | Down | Either | Ignore

    let extra_precision = ref false
    let set_precise_logging _ = (extra_precision := true)

    (* vector of zero-crossing results *)
    type zvec = int array

    let zvec_create n  = Array.make n 0

    let zvec_get zv i = zv.(i) <> 0
    let zvec_set zv i d =
      match d with
      | Up | Either -> zv.(i) <- 1
      | Down        -> zv.(i) <- -1
      | Ignore      -> zv.(i) <- 0
    let zvec_set' zv i v = zv.(i) <- v

    let zvec_log l t zv =
      if !extra_precision
      then printf "%s%.15e" l t
      else printf "%s%e" l t;
      Array.iter (printf "\t% d") zv;
      printf "\n"

    (* vector of zero-crossing expressions *)
    type zxvec = (float, Bigarray.float64_elt, Bigarray.c_layout) Bigarray.Array1.t
    let zxvec_get      = Bigarray.Array1.get
    let zxvec_set      = Bigarray.Array1.set

    let create n = Bigarray.Array1.create Bigarray.float64 Bigarray.c_layout n
    let copy     = Bigarray.Array1.blit
    let length   = Bigarray.Array1.dim

    let app f v =
      for i = 0 to (length v - 1) do
        f i (zxvec_get v i)
      done

    let fold_zxzx f acc f0 f1 =
      let n = length f0 in
      let rec fold acc i =
        if i = n then acc
        else
          let acc' = f i acc (zxvec_get f0 i) (zxvec_get f1 i) in
          fold acc' (i + 1)
      in fold acc 0

    (* return a function that looks for zero-crossings *)
    let get_check_root rdir =
      let check_up     x0 x1 = if x0 < 0.0 && x1 >= 0.0 then  1 else 0 in
      let check_down   x0 x1 = if x0 > 0.0 && x1 <= 0.0 then -1 else 0 in
      let check_either x0 x1 = if x0 < 0.0 && x1 >= 0.0 then  1 else
                               if x0 > 0.0 && x1 <= 0.0 then -1 else 0 in
      let no_check x0 x1 = 0 in

      match rdir with
      | Up     -> check_up
      | Down   -> check_down
      | Either -> check_either
      | Ignore -> no_check

    (* return a function that looks for zero-crossings between f0 and f1 *)
    let make_check_root rdir f0 f1 =
      let check = get_check_root rdir in
      (fun i -> check (zxvec_get f0 i) (zxvec_get f1 i))

    let update_roots calc_zc f0 f1 roots =
      let update i found x0 x1 =
        let zc = calc_zc x0 x1 in
        zvec_set' roots i zc;
        found || (zc <> 0)
      in
      fold_zxzx update false f0 f1

    let clear_roots roots =
      Array.fill roots 0 (Array.length roots) 0

    let log_limits f0 f1 =
      let logf i _ = printf "z| g[% 2d]: % .24e --> % .24e\n" i in
      fold_zxzx logf () f0 f1

    let zxvec_log l t zxv =
      let pr f =
        if !extra_precision
        then printf "\t% .15e"
        else printf "\t% e" in

      if !extra_precision
      then printf "%s%.15e" l t
      else printf "%s%e" l t;

      app pr zxv;
      printf "\n"

    let ignore_roots n = (zvec_create n, create n)

    let debug = ref false

    let args = [
        ("-debugz", Arg.Set debug, " Log zero-crossing searches.")
      ]

    (*
      To complete the implementation, add:
     
      type 'cvec t
      val init : int * (float -> 'cvec -> zxvec -> unit) -> 'cvec -> 'cvec t
      val reinit : 'cvec t -> float -> 'cvec -> unit
      val num_roots : 'cvec t -> int
      val set_root_directions : 'cvec t -> root_direction -> unit
      val roots : 'cvec t -> zvec
      val next_mesh : 'cvec t -> float -> 'cvec -> unit
      val find : 'cvec t -> (float -> int -> 'cvec -> unit)
                         -> 'cvec -> float option
    *)

  end (* }}} *)

module NullStateSolver : STATE_SOLVER = (* A state solver with no states *)
  struct (* {{{ *)
    include SolverInfrastructure

    type t = unit parameter_t
    let init _ _ = init_parameters () 
    let reinit _ _ _ = ()
    let step _ t _ = t
    let full_step = step
    let get_dky _ _ _ _ = ()

  end (* }}} *)

module NullZerocSolver : ZEROC_SOLVER = (* A zeroc solver with no zeroes *)
  struct (* {{{ *)
    include ZerosInfrastructure

    let empty_zvec = zvec_create 0
     
    type 'cvec t = unit
    let init _ _ = ()
    let reinit _ _ _ = ()
    let num_roots _ = 0
    let set_root_directions _ _ = ()
    let roots _ = empty_zvec
    let next_mesh _ _ _ = ()
    let find _ _ _ =  None

  end (* }}} *)

module NullSolver = Solver (NullStateSolver) (NullZerocSolver)

