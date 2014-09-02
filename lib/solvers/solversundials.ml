 
module Sundials =
struct
  module Cvode  = Cvode_serial

  type root_direction = Up | Down | Either | Ignore
  type sim_result = Roots | Continue | Stop

  exception Solvererror of string

  type cvec = Cvode.val_array

  let cvec_create n  =
    let c = Cvode.Carray.create n in
    Cvode.Carray.fill c 0.0;
    c

  let cvec_get       = Bigarray.Array1.get
  let cvec_set       = Bigarray.Array1.set
  let cvec_log l t c =
    print_string l;
    Cvode.Carray.print_with_time t c
  let cvec_copy      = Cvode.Carray.blit

  type zvec = Cvode.root_array

  (* TODO: normally, this should be:
       let zvec_get = Cvode.Roots.get
     It is set to rising at the moment to work around a bug in Sundials (reported
     upstream by email Nov-2011). *)
  let zvec_get    = Cvode.Roots.rising

  let zvec_set z i d =
    match d with
    | Down        -> Cvode.Roots.set z i Cvode.Roots.Falling
    | Ignore      -> Cvode.Roots.set z i Cvode.Roots.NoRoot
    | Up | Either -> Cvode.Roots.set z i Cvode.Roots.Rising

  let zvec_log l t z =
    Cvode.print_time (l, "") t;
    Cvode.Roots.print z

  let ignore_roots n = (Cvode.Roots.create n, Cvode.Carray.create n)

  type zxvec = Cvode.root_val_array
  let zxvec_set   = Bigarray.Array1.set
  let zxvec_log l t z =
    print_string l;
    Cvode.Carray.print_with_time t z

  type t = {
    session : Cvode.session;
    roots_in : Cvode.Roots.t;
  }

  let set_stop_time  { session = s } = Cvode.set_stop_time s
  let set_min_step   { session = s } = Cvode.set_min_step s
  let set_max_step   { session = s } = Cvode.set_max_step s
  let set_tolerances { session = s } = Cvode.ss_tolerances s
  let set_root_directions s d =
    match d with
    | Up     -> Cvode.set_all_root_directions s.session Cvode.Increasing
    | Down   -> Cvode.set_all_root_directions s.session Cvode.Decreasing
    | Either -> Cvode.set_all_root_directions s.session
                                          Cvode.IncreasingOrDecreasing
    | Ignore -> ()
  let set_precise_logging _ = Cvode.extra_precision := true

  let set_horizon_step _  =
    failwith "The Sundials solver does not support set_horizon_step."

  let lmm = ref Cvode.Adams
  let iter = ref Cvode.Functional
  let step_func = ref Cvode.normal

  let set_solver l i () =
    lmm := l;
    iter := i

  let max_num_steps = ref 0

  let basic_args neq =
    [
      ("-functional",
       Arg.Unit (set_solver Cvode.Adams Cvode.Functional),
       " sundials: (Adams, Functional)");

      ("-dense",
       Arg.Unit (set_solver Cvode.BDF (Cvode.Newton Cvode.Dense)),
       " sundials: (BDF, Dense)");

      ("-band",
       Arg.Unit (set_solver Cvode.BDF (Cvode.Newton
          (Cvode.Band { Cvode.mupper = neq; Cvode.mlower = neq }))),
       Printf.sprintf " sundials: (BDF, Band(%d, %d))" neq neq);

      ("-diag",
       Arg.Unit (set_solver Cvode.BDF (Cvode.Newton Cvode.Diag)),
       " sundials: (BDF, Diag)");

      ("-spgmr",
       Arg.Unit (set_solver Cvode.BDF
          (Cvode.Newton (Cvode.Spgmr { Cvode.pretype = Cvode.PrecNone;
                                       Cvode.maxl = 0 }))),
       " sundials: (BDF, SPGMR(Both))");

      ("-spbcg",
       Arg.Unit (set_solver Cvode.BDF
          (Cvode.Newton (Cvode.Spbcg { Cvode.pretype = Cvode.PrecNone;
                                       Cvode.maxl = 0 }))),
       " sundials: (BDF, SPBCG(Both))");

      ("-sptfqmr",
       Arg.Unit (set_solver Cvode.BDF
          (Cvode.Newton (Cvode.Sptfqmr { Cvode.pretype = Cvode.PrecNone;
                                         Cvode.maxl = 0 }))),
       " sundials: (BDF, SPTFQMR(Both))");

      ("-banded-spgmr",
       Arg.Unit (set_solver Cvode.BDF
          (Cvode.Newton (Cvode.BandedSpgmr ({ Cvode.pretype = Cvode.PrecNone;
                                              Cvode.maxl = 0 },
                                            { Cvode.mupper = neq;
                                              Cvode.mlower = neq})))),
       Printf.sprintf " sundials: (BDF, SPGMR(Both, %d, %d))" neq neq);

      ("-banded-spbcg",
       Arg.Unit (set_solver Cvode.BDF
           (Cvode.Newton (Cvode.BandedSpbcg ({ Cvode.pretype = Cvode.PrecNone;
                                               Cvode.maxl = 0 },
                                             { Cvode.mupper = neq;
                                               Cvode.mlower = neq})))),
       Printf.sprintf " sundials: (BDF, SPBCG(Both, %d, %d))" neq neq);

      ("-banded-sptfqmr",
       Arg.Unit (set_solver Cvode.BDF
           (Cvode.Newton
              (Cvode.BandedSptfqmr ({ Cvode.pretype = Cvode.PrecNone;
                                      Cvode.maxl = 0 },
                                    { Cvode.mupper = neq;
                                      Cvode.mlower = neq})))),
       Printf.sprintf " sundials: (BDF, SPTFQMR(Both, %d, %d))" neq neq);

      ("-mxstep",
       Arg.Set_int max_num_steps,
       " max. num. steps in calculating the next output time.");
  ]

  let args n_eq =
    let neq = n_eq - 1 in 
    basic_args neq @ [
      ("-onestep",
       Arg.Unit (fun () -> step_func := Cvode.one_step),
       " sundials: Solve continuous dynamics with CV_ONE_STEP (default: CV_NORMAL).");
    ]

  let print_error error_details =
    prerr_newline ();
    prerr_string "[";
    prerr_string error_details.Cvode.module_name;
    prerr_string " WARNING] ";
    prerr_string error_details.Cvode.function_name;
    prerr_newline ();
    prerr_string "  ";
    prerr_endline error_details.Cvode.error_message;
    prerr_newline ()

  let init f ((nroots, g) as gi) c  =
    if Cvode.Carray.length c == 0 then
      failwith "Sundials requires at least one continuous state!";
    let s = Cvode.init (!lmm) (!iter) f gi c in
    Cvode.set_err_handler_fn s print_error;
    if !max_num_steps > 0 then Cvode.set_max_num_steps s !max_num_steps;
    { session = s; roots_in = Cvode.Roots.create nroots }

  let reinit { session = s } t c = Cvode.reinit s t c

  let go { session = s } t c =
    let (t', result) = !step_func s t c in
    match result with
    | Cvode.RootsFound      -> (t', Roots)
    | Cvode.Continue        -> (t', Continue)
    | Cvode.StopTimeReached -> (t', Stop)

  let roots { session; roots_in } =
    Cvode.get_root_info session roots_in;
    roots_in

  let has_root = Sundials.Roots.exists
end

include Sundials

module SundialsStateSolver : Solvers.STATE_SOLVER =
  struct (* {{{ *)
    type cvec  = Cvode.val_array

    let create = cvec_create
    let get    = cvec_get
    let set    = cvec_set
    let log    = cvec_log
    let copy   = cvec_copy

    let args   = basic_args

    type t = Cvode.session * float ref
             (* session * previous time returned *)

    exception Solvererror of string

    let init f c = (Cvode.init (!lmm) (!iter) f Cvode.no_roots c, ref 0.0)

    let reinit (s, _) = Cvode.reinit s

    let set_stop_time (s, _)       = Cvode.set_stop_time s
    let set_min_step (s, _)        = Cvode.set_min_step s
    let set_max_step (s, _)        = Cvode.set_max_step s
    let set_tolerances (s, _)      = Cvode.ss_tolerances s
    let set_precise_logging (s, _) = set_precise_logging s

    let get_dky (s, _)             = Cvode.get_dky s

    let step (s, pre_tret) tl c =
      let pre_mesh = Cvode.get_current_time s in

      let tret =
        if !pre_tret < pre_mesh then
          let t' = min tl pre_mesh in
          (Cvode.get_dky s t' 0 c; t')
        else
          let mesh = fst (Cvode.one_step s tl c) in
          if tl < mesh then (Cvode.get_dky s tl 0 c; tl) else mesh
      in
      pre_tret := tret;
      tret

    let full_step (s, pre_tret) tl c =
      let tret = fst (Cvode.normal s tl c) in
      pre_tret := tret;
      tret

  end (* }}} *)

open Solvers

let _ =
  Zlsolve.register
    "sundials"
    "external Sundials CVODE solver with custom zero-crossing detection"
    (module Solver (SundialsStateSolver) (Illinois) : SOLVER)

let _ =
  Zlsolve.register
    "sundials-native-zero-crossings"
    "external solver: Sundials CVODE with built-in zero-crossing detection"
    (module Sundials : SOLVER)

let _ =
  Fixedstep.register
    "sundialsF"
    "external Sundials CVODE solver with fixed steps"
    (module SundialsStateSolver : STATE_SOLVER)

