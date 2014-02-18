
let time_eq  = Solvers.time_eq
let time_leq = Solvers.time_leq
let time_geq = Solvers.time_geq

let custom_args = ref ([] : (Arg.key * Arg.spec * Arg.doc) list)

(* Add another argument to the list returned by args *)
let add_custom_arg arg =
  custom_args := arg :: !custom_args

let printf = Printf.printf
let eprintf = Printf.eprintf

let black   = "\x1b[0m"
let red     = "\x1b[31m"
let green   = "\x1b[32m"
let yellow  = "\x1b[33m"
let blue    = "\x1b[34m"
let magenta = "\x1b[35m"
let cyan    = "\x1b[36m"
let gray    = "\x1b[37m"

(* The simulation algorithm *)

module type ZELUS_SOLVER =
  sig (* {{{ *)

    (** Interface for compiled functions: SEE zlsolve.mli *)

    type cvector  (* array of continuous states *)
    type zvector  (* array of zero-crossing flags *)
    type zxvector (* array of zero-crossing values *)

    val get_cs : cvector  -> int -> float
    val set_cs : cvector  -> int -> float -> unit
    val get_zc : zvector  -> int -> bool
    val set_zx : zxvector -> int -> float -> unit

    type 'a single_f =
      cvector * cvector * zxvector * zvector * bool * float -> 'a * bool * float

    type model_der = cvector * cvector -> unit

    type model_zero = cvector * zxvector -> unit

    type model_disc_next =
      | Continue of bool * float
      | Goagain of bool
      | EndSimulation

    type 'a model_disc = cvector * zvector * float -> 'a * model_disc_next

    type 'a compiled_model = {
      f_der : model_der;
      f_zero : model_zero;
      f_disc : 'a model_disc;
      num_cstates : unit -> int;
      num_zeros : unit -> int;
    }

    val split_single : int -> int -> 'a single_f -> 'a compiled_model

    (** Configuring and calling the D-C solver *)

    (* Log simulation steps and continuous state values. *)
    val enable_logging       : unit -> unit

    (* The solver's minimum and maxmium step sizes. *)
    val min_step_size : float option ref
    val max_step_size : float option ref

    (* The maximum simulation time. *)
    val max_sim_time  : float option ref

    type 'a sim_state

    val main  : 'a compiled_model -> 'a sim_state
    val main' : (int * int) -> 'a single_f -> 'a sim_state

    (* The result returned by step is [None] after a continuous step and
     * [Some x] after a discrete step, where [x] is the value returned by
     * the main function.
     *)
    val step      : 'a sim_state -> 'a option * 'a sim_state
    val is_done   : 'a sim_state -> bool


    (** Adding command-line arguments *)

    (* Given the number of continuous states in the system being simulated, return a
     * list that can be passed to Arg.parse to allow simulation parameters to be set
     * at the command line. *)
    val args : int -> (Arg.key * Arg.spec * Arg.doc) list
  end (* }}} *)

module Instantiate (Solver : Solvers.SOLVER) =
  struct (* {{{ *)

    (** Interface for compiled functions **)

    type cvector  = Solver.cvec
    type zvector  = Solver.zvec
    type zxvector = Solver.zxvec

    let get_cs = Solver.cvec_get
    let set_cs = Solver.cvec_set
    let get_zc = Solver.zvec_get
    let set_zx = Solver.zxvec_set

    type 'a single_f =
      cvector * cvector * zxvector * zvector * bool * float -> 'a * bool * float

    type model_der = cvector * cvector -> unit

    type model_zero = cvector * zxvector -> unit

    type model_disc_next =
      | Continue of bool * float
      | Goagain of bool
      | EndSimulation

    type 'a model_disc = cvector * zvector * float -> 'a * model_disc_next

    type 'a compiled_model = {
      f_der : model_der;
      f_zero : model_zero;
      f_disc : 'a model_disc;
      num_cstates : unit -> int;
      num_zeros : unit -> int;
    }

    (* the value of time passed to main_f when it is executed inside the solver *)
    let no_time_in_solver = -1.0

    let split_single n_cstates n_zeros main =
      let (no_roots_in, ignore_roots_out) = Solver.ignore_roots n_zeros in
      let ignore_der = Solver.cvec_create n_cstates in

      let der_f (x, dx) =
        ignore (main
          (x, dx, ignore_roots_out, no_roots_in, false, no_time_in_solver))

      and zero_f (x, ze) =
        ignore (main
          (x, ignore_der, ze, no_roots_in, false, no_time_in_solver))

      and disc_f (x, z, t) =
        let result, goagain, t_horizon =
            main (x, ignore_der, ignore_roots_out, z, true, t)
        in
        if goagain then (result, Goagain true)
        else (result, Continue (true, t_horizon))

      in
      {
        f_der = der_f;
        f_zero = zero_f;
        f_disc = disc_f;
        num_cstates = (fun () -> n_cstates);
        num_zeros = (fun () -> n_zeros);
      }

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
     * thus it cannot simply default to max_float or infinity. Even just very high
     * values (e.g. 1.0e20) will cause problems, like missed zero-crossings,
     * because they influence the behaviour of the solver. *)
    let max_c_step    = ref 100.0

    let rel_tol       = ref (None : float option)
    let abs_tol       = ref (None : float option)

    let log           = ref false
    let log_gcalls    = ref false
    let log_fcalls    = ref false

    let show_stats    = ref false

    let enable_logging ()       = (log := true)

    let set_param set_fn s param =
      (match !param with Some v -> set_fn s v | _ -> ())

    let set_param2 set_fn s param1 param2 =
      (match !param1, !param2 with Some v1, Some v2 -> set_fn s v1 v2 | _ -> ())

    (** Logging functions **)

    let set_color s = if !color_logging then print_string s

    let print_time (s1, s2) t =
      if !precise_logging
      then Printf.printf "%s%.15e%s" s1 t s2
      else Printf.printf "%s%e%s" s1 t s2

    let print_roots t rin =
      if !log then (set_color green;
                    Solver.zvec_log "Z : " t rin;
                    set_color black)

    let print_states label t cs =
      if !log then Solver.cvec_log label t cs

    let print_horizon t t_horizon reinit =
      if !log then begin
        set_color yellow;
        print_time ("H : ", " ") t;
        print_time ("\t horizon=",
          if reinit then " (reinit)\n" else "\n") t_horizon;
        set_color black;
        flush stdout
      end

    let print_help_key () =
      if !log then begin
        print_endline "";
        print_endline "  C : result of continuous solver";
        print_endline "  C': state given to the discrete solver (last values)";
        set_color green;
        print_endline "  Z : zero-crossings triggering the discrete solver";
        set_color black;
        print_endline "  D : result of discrete solver";
        set_color yellow;
        print_endline "  H : time horizon set for a continuous phase";
        set_color black;
        print_endline "";

        print_string "M : time";
        print_newline ();

        print_string "--+\n"
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

    (** Execution algorithm **)

    type 'a sim_state =
      | SimCont of (unit -> ('a option * 'a sim_state))
      | SimEnd

    let main { f_der; f_zero; f_disc; num_cstates; num_zeros } =
      let n_cstates = num_cstates ()
      and n_zeros   = ref (num_zeros ()) in

      let cstates     = Solver.cvec_create n_cstates
      and cder        = Solver.cvec_create n_cstates
      and pre_cstates = Solver.cvec_create
                          (if !always_reinit then 0 else n_cstates)
      and no_roots_in = ref (fst (Solver.ignore_roots !n_zeros))
      in

      let f_main t cs ds =
        f_der (cs, ds);
        if !log_fcalls then begin
          set_color gray;
          Solver.cvec_log  "*FC:" t cs;
          Solver.cvec_log  "*FD:" t ds;
          set_color black;
        end in

      let g_main t cs rs =
        f_zero (cs, rs);
        if !log_gcalls then begin
          set_color gray;
          Solver.cvec_log  "*ZC:" t cs;
          Solver.zxvec_log " ZR:" t rs;
          set_color black;
        end in

      let d_main t rin = f_disc (cstates, rin, t) in

      (* This function must be called before entering a sequence of discrete
         steps to ensure that "continuous pre"s within the program are set
         correctly (since the solver will normally have called the program for a
         later time, and then back interpolated for the requested time). In
         addition, when always_reinit=false, it is needed to set the value of
         pre_cstates. *)
      let setup_discrete_step t =
          f_main no_time_in_solver cstates cder;
          if not !always_reinit then Solver.cvec_copy cstates pre_cstates
        in

      let exists_state_reset () =
        let rec check i =
          if i = n_cstates then false
          else if Solver.cvec_get cstates i <> Solver.cvec_get pre_cstates i
          then true
          else check (i + 1) in
        !always_reinit || check 0 in

      let rec init () = begin
          (* INITIAL CALL *)
          let goagain, t_horizon =
            match snd (d_main 0.0 !no_roots_in) with
            | Continue (_, t_horizon) -> (false, t_horizon)
            | Goagain reset -> (true, infinity)
            | EndSimulation -> failwith "End of simulation at first call!" in
          
          if goagain && not !always_reinit
            then Solver.cvec_copy cstates pre_cstates;

          let s = Solver.init f_main (!n_zeros, g_main) cstates in

          Solver.set_root_directions s Solver.Up;

          set_param  Solver.set_stop_time  s max_sim_time;
          set_param  Solver.set_min_step   s min_step_size;
          set_param  Solver.set_max_step   s max_step_size;
          set_param2 Solver.set_tolerances s rel_tol abs_tol;
          if !precise_logging then Solver.set_precise_logging s;

          print_help_key ();
          print_states (if goagain then "I.: " else "I : ") 0.0 cstates;
          print_horizon 0.0 t_horizon false;

          if goagain
          then SimCont (discrete' s 0.0 !no_roots_in false false)
          else SimCont (continuous s 0.0 t_horizon)
        end

      and continuous s t t_horizon () =
        try
          (* CONTINUOUS CALL(S) *)
          let t_limit = min (t +. !max_c_step) t_horizon in
          let (t', result) = Solver.go s t_limit cstates in

          print_states
            (if result = Solver.Roots
                || t' >= t_horizon then "C': " else "C : ") t' cstates;

          match result with
          | Solver.Continue when (t' < t_horizon) ->
              (None, SimCont (continuous s t' t_horizon))

          | Solver.Roots | Solver.Continue ->
              (None, SimCont (discrete s t'))

          | Solver.Stop ->
              (print_terminated t; (None, SimEnd))
        with Solver.Solvererror err ->
              (eprintf "fatal solver error: %s\n" err; (None, SimEnd))

      and discrete s t () = begin
          setup_discrete_step t;

          let roots_in = Solver.roots s in
          print_roots t roots_in;
          discrete' s t roots_in false false ()
        end

      and discrete' s t roots_in needs_reset needs_rootfn () =
        (* DISCRETE CALL *)
        let (result, next) = d_main t roots_in in

        let pre_nzeros = !n_zeros
        and n_zeros' = num_zeros () in
        if n_zeros' <> pre_nzeros then begin
          n_zeros := n_zeros';
          no_roots_in := fst (Solver.ignore_roots !n_zeros)
        end;

        match next with
        | Continue (reset, t_horizon) ->
            let reset = needs_reset || reset in
            begin
              print_states "D : " t cstates;
              let needs_reinit = reset && exists_state_reset () in
              print_horizon t t_horizon needs_reinit;

              if needs_rootfn then
                (* Solver.reinit_roots s !n_zeros g_main *)
                failwith "reinit_roots is not yet implemented!"
                ;
              if needs_reinit then Solver.reinit s t cstates;

              (Some result, SimCont (continuous s t t_horizon))
            end

        | Goagain reset ->
            let reset = needs_reset || reset in
            begin
              print_states "D.: " t cstates;
              (Some result, SimCont (discrete' s t !no_roots_in reset
                                               (pre_nzeros <> !n_zeros)))
            end

        | EndSimulation -> begin
              print_states "D$: " t cstates;
              print_terminated t;
              (Some result, SimEnd)
            end
      in
      init ()

    let main' (ns, nz) main_f =
      let model = split_single ns nz main_f in
      main model

    let step x =
      match x with
      | SimCont f -> f ()
      | SimEnd -> (None, x)

    let is_done x =
      match x with
      | SimEnd    -> true
      | SimCont _ -> false

    (** command-line arguments **)

    let args n_eq =
      Arg.align (
      !custom_args @ Solver.args n_eq @
      [
        ("-maxt",
         Arg.Float (fun m -> max_sim_time := Some m),
         "<float> maximum simulation time");

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

        ("-stats",
         Arg.Set show_stats,
         " Show statistics on termination (with -maxt).");
    ])

  end (* }}} *)

let add_epsilons num_eps v =
  v +. (float(num_eps)
        *. (if v = 0.0 then min_float else abs_float v)
        *. epsilon_float
        *. 100.0)

let float_with_delta_of_string s =
  let tally = ref 0 in

  let count_deltas c =
    if c == '+' then incr tally
    else if c == '-' then decr tally
  in

  let f = Scanf.sscanf s "%e%s" (fun f s -> (String.iter count_deltas s; f))
  in
  add_epsilons !tally f

let set_float_delta fr =
  Arg.String (fun s -> fr := float_with_delta_of_string s)

(* Solver registration and instantiation *)

let solver  = ref ""
let set_default_solver name = (solver := name)

let solvers : (string, (module Solvers.SOLVER)) Hashtbl.t = Hashtbl.create 17

let register' name ((key, spec, doc) as arg) smodule =
  let arg = if name = !solver then (key, spec, doc ^ " (default)") else arg in
  Hashtbl.add solvers name smodule;
  add_custom_arg arg

let register name doc smodule =
  let arg = ("-" ^ name, Arg.Unit (fun () -> solver := name), " " ^ doc) in
  register' name arg smodule

let instantiate () =
  try
    let module S = (val Hashtbl.find solvers !solver : Solvers.SOLVER) in
    (module Instantiate (S) : ZELUS_SOLVER)
  with Not_found -> failwith (Printf.sprintf
              "The library does not contain the '%s' numeric solver!" !solver)

let check_for_solver argv =
  let skip_one = ref true in  (* skip the program name *)
  let skip_all = ref false in
  let check_arg arg =
    if !skip_all then ()
    else if !skip_one  then skip_one := false
    else if arg = "--" then skip_all := true
    else if arg = "-"  then skip_one := true
    else if String.get arg 0 <> '-' then ()
    else
      let name = String.sub arg 1 (String.length arg - 1) in
      if Hashtbl.mem solvers name then solver := name
  in
  Array.iter check_arg argv

