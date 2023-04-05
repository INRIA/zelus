
let printf = Printf.printf
let eprintf = Printf.eprintf

let black             = "\x1b[0;0m"
let red               = "\x1b[0;31m"
let boldred           = "\x1b[1;31m"
let green             = "\x1b[0;32m"
let yellow            = "\x1b[0;33m"
let blue              = "\x1b[0;34m"
let magenta           = "\x1b[0;35m"
let cyan              = "\x1b[0;36m"
let gray              = "\x1b[0;37m"
let before_loggedcall = cyan
let after_loggedcall  = cyan

(* The simulation algorithm *)

module type ZELUS_SOLVER =
sig (* {{{ *)
  (** Interface for compiled functions *)

  (** Configuring and calling the D-C solver *)

  (* Log simulation steps and continuous state values. *)
  val enable_logging       : unit -> unit

  (* The solver's minimum and maximum step sizes. *)
  val min_step_size : float option ref
  val max_step_size : float option ref

  (* The maximum simulation time. *)
  val max_sim_time  : float option ref

  (* A factor relating simulation and wall clock times. *)
  val speedup       : float ref

  val step  :    's Zls.f_alloc
              -> 's Zls.f_csize
              -> 's Zls.f_zsize
              -> 's Zls.f_horizon
              -> 's Zls.f_maxsize
              -> 's Zls.f_ders
              -> ('s, 'o) Zls.f_step
              -> 's Zls.f_zero
              -> 's Zls.f_reset
              -> (unit -> 'o option * bool * float)

end (* }}} *)

module Make (SSolver : Zls.STATE_SOLVER) 
            (ZSolver : Zls.ZEROC_SOLVER) =
struct (* {{{ *)

  (** Interface for compiled functions **)

  (* the value of time passed to main_f when it is executed inside the solver *)
  let no_time_in_solver = -1.0

  (* increment a given horizon by a small margin *)
  let add_margin h = h +. (2.0 *. epsilon_float *. h)
						  
  (** Configurable settings **)

  let max_sim_time    = ref None
  let min_step_size   = ref None
  let max_step_size   = ref None
  let always_reinit   = ref true
  let precise_logging = ref false
  let color_logging   = ref true

  (* The maximum amount of simulation time that may pass within a C step, i.e.
   * within a single call to the solver. Experience shows that Cvode.normal
   * returns incorrect t' results if this value is too large (i.e. ~1.0e35), and
   * thus it cannot simply default to max_float or infinity. Even just a very
   * high values (e.g. 1.0e20) may cause problems, like missed zero-crossings,
   * because it influences the behaviour of the solver. *)
  let max_c_step    = ref 100.0

  let rel_tol       = ref (None : float option)
  let abs_tol       = ref (None : float option)

  let log           = ref false
  let log_gcalls    = ref false
  let log_fcalls    = ref false
  let log_dcalls    = ref false

  let show_stats    = ref false

  let speedup       = ref 1.0

  let enable_logging ()       = (log := true)

  let set_param set_fn s param =
    (match !param with Some v -> set_fn s v | _ -> ())

  let set_param2 set_fn s param1 param2 =
    (match !param1, !param2 with Some v1, Some v2 -> set_fn s v1 v2 | _ -> ())

  (** Logging functions **)

  let set_color s = if !color_logging then print_string s
  let set_err_color s = if !color_logging then prerr_string s

  let print_time (s1, s2) t =
    if !precise_logging
    then Printf.printf "%s%.15e%s" s1 t s2
    else Printf.printf "%s%e%s" s1 t s2

  let print_black_newline () = set_color black; print_newline (); flush stdout
  let print_black_endline s = print_string s; print_black_newline ()

  let carray_log l t c =
    let pr = if !precise_logging then printf "\t% .15e" else printf "\t% e" in
    if !precise_logging then printf "%s%.15e" l t else printf "%s%e" l t;
    for i = 0 to Bigarray.Array1.dim c -1 do
      pr c.{i}
    done;
    print_black_newline ()

  let zarray_log l t z =
    if !precise_logging then printf "%s%.15e" l t else printf "%s%e" l t;
    for i = 0 to Bigarray.Array1.dim z - 1 do
      printf "\t%s" (Int32.to_string z.{i})
    done;
    print_black_newline ()

  let print_roots zs t rin =
    if !log then (set_color boldred;
                  zarray_log "Z : " t rin)

  let print_states label t cs =
    if !log then carray_log label t cs

  let print_horizon t t_horizon reinit =
    if !log then begin
      set_color yellow;
      print_time ("H : ", " ") t;
      print_time ("\t horizon=",
        if reinit then " (reinit)" else "") t_horizon;
      print_black_newline ()
    end

  let print_help_key () =
    if !log then begin
      print_endline "";
      print_endline "  I : initial solver state";
      print_endline "  C : result of continuous solver";
      print_endline "  C': state given to the discrete solver (last values)";
      set_color boldred;
      print_black_endline "  Z : zero-crossings triggering the discrete solver";
      print_endline "  D : result of discrete solver";
      set_color yellow;
      print_black_endline "  H : time horizon set for a continuous phase";
      print_newline ();

      print_string "M : time";
      print_newline ();

      print_string "--+\n";
      flush stdout
    end

  let print_terminated t =
    if !log then begin
      print_time ("--+ terminated at ", "\n") t;
      flush stdout
    end;
    if !show_stats then begin
      let stats = Gc.stat () in
      printf "gc collections: minor=%d major=%d compact=%d\n"
        stats.Gc.minor_collections
        stats.Gc.major_collections
        stats.Gc.compactions;
      printf "gc words: minor=%.0f promoted=%.0f major=%.0f\n"
        stats.Gc.minor_words
        stats.Gc.promoted_words
        stats.Gc.major_words;
      flush stdout
    end

  (* Given the number of continuous states in the system being simulated,
   * return a list that can be passed to Arg.parse to allow simulation
   * parameters to be set at the command line. *)
  let args n_eq =
    Arg.align (
    [
      ("-maxt",
       Arg.Float (fun m -> max_sim_time := Some m),
       "<float> maximum simulation time");

      ("-speedup",
       Arg.Float (fun m -> speedup := m),
       "<float> relate simulation and wall clock times (2.0 = twice as fast)");

      ("-fullspeed",
       Arg.Unit (fun () -> speedup := 0.0),
       " Do not try to relate simulation and wall clock times");

      ("-maxcstep",
       Arg.Float (fun m -> max_c_step := m),
       "<float> maximum length of a C step (if 'too big' the solver may behave strangely)");

      ("-maxstep",
       Arg.Float (fun m -> max_step_size := Some m),
       "<float> maximum step size (of solver)");

      ("-minstep",
       Arg.Float (fun m -> min_step_size := Some m),
       "<float> minimum step size (of solver)");

      ("-reltol",
       Arg.Float (fun t -> rel_tol := Some t),
       "<float> Set relative tolerance (only effective if -abstol is also given).");

      ("-abstol",
       Arg.Float (fun t -> abs_tol := Some t),
       "<float> Set absolute tolerance (only effective if -reltol is also given).");

      ("-precisetime",
       Arg.Set precise_logging,
       " Log time values with higher precision.");

      ("-nocolor",
       Arg.Clear color_logging,
       " Disable color logging (no ASCII escape sequences).");

      ("-avoidreinit",
       Arg.Clear always_reinit,
       " Only reinitialize the solver when continuous state values change.");

      ("-l",
       Arg.Set log,
       " Log state variables and zero-crossings to stdout.");

      ("-lgcalls",
       Arg.Set log_gcalls,
       " Log zero-crossing function calls to stdout.");

      ("-lfcalls",
       Arg.Set log_fcalls,
       " Log differential function calls to stdout.");
                    
      ("-ldcalls",
       Arg.Set log_dcalls,
       " Log discrete function calls to stdout.");

      ("-stats",
       Arg.Set show_stats,
       " Show statistics on termination (with -maxt).");
  ])

  (** Execution algorithm **)

  type model_disc_next =
    | Continue of bool * float
    | Goagain of bool
    | EndSimulation

  type sim_state_i = {
    discrete_ready : bool;
    reset_required : bool;
    init_horizon   : float;
  }

  type sim_state_d = {
    ssolver     : SSolver.t; (* session with the state solver *)
    zsolver     : ZSolver.t; (* session with the zero-crossing solver *)
    t_sim       : float;     (* time at the start of a step *)
    t_nextmesh  : float;     (* maximum time calculated by the solver *)
    t_horizon   : float;     (* horizon for the next solver step *)
    after_c     : bool;      (* the mode at the last step was C *)
    roots_valid : bool;      (* the roots array contains valid data *)
    needs_reset : bool;      (* the solver must be reset *)
  }

  type sim_state =
    | SimI of sim_state_i
    | SimD of sim_state_d
    | SimC of sim_state_d
    | SimF

  let step (f_alloc   : 's Zls.f_alloc)
           (f_csize   : 's Zls.f_csize)
           (f_zsize   : 's Zls.f_zsize)
           (f_horizon : 's Zls.f_horizon)
           (f_maxsize : 's Zls.f_maxsize)
           (f_ders    : 's Zls.f_ders)
           (f_step    : ('s, 'o) Zls.f_step)
           (f_zero    : 's Zls.f_zero)
           (f_reset   : 's Zls.f_reset)
    =
    let dstate = f_alloc () in
    let n_cstates, n_zeros = f_maxsize dstate in
    Arg.parse (args n_cstates) (fun _ -> ())
      "Zélus simulation loop";

    let no_roots_in = Zls.zmake n_zeros in
    let no_roots_out = Zls.cmake n_zeros in
    let roots = Zls.zmake n_zeros in
    let ignore_der = Zls.cmake n_cstates in

    let cstates_nv  = SSolver.cmake n_cstates in
    let cstates     = SSolver.unvec cstates_nv in
    let pre_cstates = Zls.cmake (if !always_reinit then 0 else n_cstates) in

    let f_main t cs ds =
      if !log_fcalls then begin
        set_color before_loggedcall;
        carray_log "*FC:" t cs;
        ignore (f_ders dstate cs ds no_roots_in no_roots_out no_time_in_solver);
        set_color after_loggedcall;
        carray_log " FD:" t ds
      end else ignore (f_ders dstate cs ds no_roots_in no_roots_out no_time_in_solver);
    in

    let g_main t cs rs =
      if !log_gcalls then begin
        set_color before_loggedcall;
        carray_log "*ZC:" t cs;
        ignore (f_zero dstate cs no_roots_in rs no_time_in_solver);
        set_color after_loggedcall;
        carray_log " ZR:" t rs
      end else ignore (f_zero dstate cs no_roots_in rs no_time_in_solver);
    in

    let g_setup t cs ri =
      if !log_gcalls then begin
        set_color before_loggedcall;
        carray_log "*ZS:" t cs;
        ignore (f_zero dstate cs ri no_roots_out no_time_in_solver);
        set_color after_loggedcall
      end else ignore (f_zero dstate cs ri no_roots_out no_time_in_solver);
    in

    let d_main t rin =
      (* TODO: need to pass a single dout vector; solvers should not use two
       * either! *)
      let o =
        if !log_dcalls then begin
          set_color before_loggedcall;
          carray_log "*DC:" t cstates;
          let r = f_step dstate cstates ignore_der (* rin *) no_roots_in t in
          set_color after_loggedcall;
          carray_log " DR:" t cstates;
          r
        end else f_step dstate cstates ignore_der (* rin *) no_roots_in t
      in
      let t_horizon = f_horizon dstate in
      if t_horizon <= t then o, Goagain true
      else o, Continue (true, t_horizon)
    in

    let simstate = ref (SimI { discrete_ready = false;
                               reset_required = true;
                               init_horizon = 0.0 }) in
      
    (* This function must be called before entering a sequence of discrete
       steps to ensure that "continuous pre"s within the program are set
       correctly (since the solver will normally have called the program for a
       later time, and then back interpolated for the requested time). In
       addition, when always_reinit=false, it is needed to set the value of
       pre_cstates. *)
    let setup_discrete_step t roots =
        g_setup no_time_in_solver cstates roots;
        if not !always_reinit then Bigarray.Array1.blit cstates pre_cstates
      in

    let exists_state_reset () =
      let rec check i =
        if i = n_cstates then false
        else if cstates.{i} <> pre_cstates.{i}
        then true
        else check (i + 1) in
      !always_reinit || check 0 in

    let step () =
      match !simstate with
      | SimI { discrete_ready = false; reset_required } -> begin
	  (** Basics.set_major_step true; **)

          (* INITIAL CALL: first part, discrete steps *)
          if reset_required then begin
            print_help_key ();
            f_reset dstate
          end;

          let step_out, step_status = d_main 0.0 no_roots_in in
          let goagain, t_horizon = match step_status with
            | Continue (_, t_horizon) -> (false, t_horizon)
            | Goagain reset -> (true, infinity)
            | EndSimulation -> failwith "End of simulation at first call!" in

          print_states (if goagain then "D.: " else "D : ") 0.0 cstates;
          print_horizon 0.0 t_horizon false;

          simstate := SimI { discrete_ready = not goagain;
                             reset_required = false;
                             init_horizon = t_horizon };
          Some step_out, false, 0.0
        end

      | SimI { discrete_ready = true; init_horizon } -> begin
          (* INITIAL CALL: second part, solver initialization *)
	  (** Basics.set_major_step true; **)

          if not !always_reinit
            then Bigarray.Array1.blit cstates pre_cstates;

          let ss = SSolver.initialize f_main cstates_nv in
          let zs = ZSolver.initialize n_zeros g_main cstates in
          set_param  SSolver.set_stop_time  ss max_sim_time;
          set_param  SSolver.set_min_step   ss min_step_size;
          set_param  SSolver.set_max_step   ss max_step_size;
          set_param2 SSolver.set_tolerances ss rel_tol abs_tol;

          print_states "I : " 0.0 cstates;
          print_horizon 0.0 init_horizon false;

          let params = {
            ssolver     = ss;
            zsolver     = zs;
            t_sim       = 0.0;
            t_nextmesh  = 0.0;
            t_horizon   = init_horizon;
            after_c     = false;
            roots_valid = false;
            needs_reset = false;
          } in
          simstate := SimC params;
          None, false, 0.0
        end

      | SimC ({ ssolver = ss; zsolver = zs; t_sim = last_t;
                t_nextmesh; t_horizon; needs_reset } as params) -> (try
          (* CONTINUOUS CALL(S) *)
	  (** Basics.set_major_step false; **)

          if needs_reset then (SSolver.reinitialize ss last_t cstates_nv;
                               ZSolver.reinitialize zs last_t cstates);

          let t_limit = min (last_t +. !max_c_step) t_horizon in
          let t_nextmesh =
            if needs_reset || t_limit > t_nextmesh
            then SSolver.step ss (add_margin t_limit) cstates_nv
            else t_nextmesh in

          (* interpolation if the mesh point has passed the time limit *)
	  let t = if t_limit < t_nextmesh
                  then (SSolver.get_dky ss cstates_nv t_limit 0; t_limit)
                  else t_nextmesh
          in

          ZSolver.step zs t cstates;

          (* TODO: should zero-crossings search a little to the right? *)
          let has_roots = ZSolver.has_roots zs in
          let t =
            if has_roots
            then ZSolver.find zs (SSolver.get_dky ss cstates_nv, cstates) roots
            else t in

          let event = has_roots || t >= t_horizon in
          let delta =
            if !speedup > 0.0 then (t -. last_t) /. !speedup else 0.0 in

          print_states (if event then "C': " else "C : ") t cstates;

          let at_stop_time =
            match !max_sim_time with Some tmax -> t >= tmax | _ -> false in

          simstate :=
            if at_stop_time then (print_terminated t; SimF)
            else if event then begin
                if has_roots then print_roots zs t roots;
                setup_discrete_step t (if has_roots
                                       then roots else no_roots_in);
                SimD { params with t_sim = t;
                                   t_nextmesh = t_nextmesh;
                                   after_c = true;
                                   roots_valid = has_roots;
                                   needs_reset = false; }
              end
            else SimC { params with needs_reset = false;
                                    after_c = true;
                                    t_sim = t;
                                    t_nextmesh = t_nextmesh };
          None, false, delta

        with err -> begin
          flush stdout;
          set_err_color boldred;
          eprintf "fatal error: %s\n" (Printexc.to_string err);
          if !log then
            if Printexc.backtrace_status ()
            then Printexc.print_backtrace stderr
            else prerr_string
              "(compile with -g and run with OCAMLRUNPARAM=b for a backtrace)\n";
          Printexc.print_backtrace stderr;
          set_err_color black;
          flush stderr;
          simstate := SimF;
          None, false, 0.0
        end)

      | SimD ({ ssolver = ss; zsolver = zs;
                t_sim; after_c; needs_reset; roots_valid } as params) -> begin
          (* DISCRETE CALL *)
	  (** Basics.set_major_step true; **)

          let step_out, step_status = d_main t_sim no_roots_in in
          simstate := (match step_status with
            | Continue (reset, t_horizon) -> begin
                  print_states "D : " t_sim cstates;
                  let needs_reinit =
                        needs_reset || reset && exists_state_reset () in
                  print_horizon t_sim t_horizon needs_reinit;
                  SimC { params with after_c = false;
                                     t_horizon = t_horizon;
                                     needs_reset = needs_reinit }
                end

            | Goagain reset -> begin
                  print_states "D.: " t_sim cstates;
                  SimD { params with after_c = false;
                                     needs_reset = needs_reset || reset }
                end

            | EndSimulation -> begin
                  print_states "D$: " t_sim cstates;
                  print_terminated t_sim;
                  SimF
                end);
          Some step_out, false, 0.0
        end

      | SimF -> None, true, 0.0
    in
    step

end (* }}} *)

