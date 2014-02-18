(***********************************************************************)
(*                                                                     *)
(*              Ocaml interface to Sundials CVODE solver               *)
(*                                                                     *)
(*           Timothy Bourke (INRIA) and Marc Pouzet (LIENS)            *)
(*                                                                     *)
(*  Copyright 2013 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file LICENSE.        *)
(*                                                                     *)
(***********************************************************************)

include Cvode

type 'a nvector = 'a Nvector.nvector

type root_array = Sundials.Roots.t
type root_val_array = Sundials.Roots.val_array


type 'a single_tmp = 'a
type 'a triple_tmp = 'a * 'a * 'a

type ('t, 'a) jacobian_arg =
  {
    jac_t   : float;
    jac_y   : 'a;
    jac_fy  : 'a;
    jac_tmp : 't
  }

type 'a callback_solve_arg =
  {
    rhs   : 'a;
    gamma : float;
    delta : float;
    left  : bool;
  }

type cvode_mem
type cvode_file
type 'a session = {
        cvode      : cvode_mem;
        user_data  : int;
        neqs       : int;
        nroots     : int;
        err_file   : cvode_file;

        mutable rhsfn      : float -> 'a -> 'a -> unit;
        mutable rootsfn    : float -> 'a -> root_val_array -> unit;
        mutable errh       : error_details -> unit;
        mutable errw       : 'a -> 'a -> unit;
        mutable jacfn      : ('a triple_tmp, 'a) jacobian_arg -> Densematrix.t -> unit;
        mutable bandjacfn  : ('a triple_tmp, 'a) jacobian_arg -> int -> int
                               -> Bandmatrix.t -> unit;
        mutable presetupfn : ('a triple_tmp, 'a) jacobian_arg -> bool -> float -> bool;
        mutable presolvefn : ('a single_tmp, 'a) jacobian_arg -> 'a callback_solve_arg
                               -> 'a nvector -> unit;
        mutable jactimesfn : ('a single_tmp, 'a) jacobian_arg -> 'a -> 'a -> unit;
      }

(* interface *)

external session_finalize : 'a session -> unit
    = "c_session_finalize"

external external_init
    : lmm -> iter -> 'a nvector -> int -> int -> float -> (cvode_mem * cvode_file)
    = "c_nvec_init_bytecode" "c_nvec_init"

external set_user_data : 'a session -> unit
    = "c_set_user_data"

(*
 * The session_table is used for sharing session values with C functions. The
 * functions do not care about the type of the underlying nvector representation
 * (i.e., the 'a in 'a session) and we want to use a single (weak) lookup table
 * to store all "'a session"s, we therefore cheat with Obj.repr.
 *
 * Only C functions and init' may call add_session/get_session. The latter is
 * explicitly type constrained to ensure consistency between type variables in
 * the callback functions, the initial vector, and the resulting session type.
 *)
module SessionTable : sig
    val proto_init :
        lmm
        -> iter
        -> (float -> 'a -> 'a -> unit)
        -> (int * (float -> 'a -> root_val_array -> unit))
        -> (int * 'a nvector)
        -> float
        -> 'a session
  end = 
  struct

  let session_table = ref (Weak.create 10 : Obj.t Weak.t)

  let add_session cvode neqs nroots err_file =
    let length = Weak.length !session_table in
    let rec find_next i =
      if i < length
      then (if Weak.check !session_table i then find_next (i + 1) else i)
      else
        let session_table' = Weak.create (2 * length) in
        Weak.blit !session_table 0 session_table' 0 length;
        session_table := session_table';
        i in
    let idx = find_next 0 in
    let session = {
          cvode      = cvode;
          user_data  = idx;
          neqs       = neqs;
          nroots     = nroots;
          err_file   = err_file;

          rhsfn      = (fun _ _ _ -> ());
          rootsfn    = (fun _ _ _ -> ());
          errh       = (fun _ -> ());
          errw       = (fun _ _ -> ());
          jacfn      = (fun _ _ -> ());
          bandjacfn  = (fun _ _ _ _ -> ());
          presetupfn = (fun _ _ _ -> false);
          presolvefn = (fun _ _ _ -> ());
          jactimesfn = (fun _ _ _ -> ());
        } in
    Weak.set !session_table idx (Some (Obj.repr session));
    session

  let get_session idx =
    match Weak.get !session_table idx with
      None -> raise Not_found
    | Some s -> Obj.obj s

  let session_rhsfn idx      = (get_session idx).rhsfn
  let session_errh idx       = (get_session idx).errh
  let session_errw idx       = (get_session idx).errw
  let session_jacfn idx      = (get_session idx).jacfn
  let session_bandjacfn idx  = (get_session idx).bandjacfn
  let session_presetupfn idx = (get_session idx).presetupfn
  let session_presolvefn idx = (get_session idx).presolvefn
  let session_jactimesfn idx = (get_session idx).jactimesfn

  let _ = Callback.register "c_nvec_cvode_ml_session"    get_session;
          Callback.register "c_nvec_cvode_ml_rhsfn"      session_rhsfn;
          Callback.register "c_nvec_cvode_ml_errh"       session_errh;
          Callback.register "c_nvec_cvode_ml_errw"       session_errw;
          Callback.register "c_nvec_cvode_ml_jacfn"      session_jacfn;
          Callback.register "c_nvec_cvode_ml_bandjacfn"  session_bandjacfn;
          Callback.register "c_nvec_cvode_ml_presetupfn" session_presetupfn;
          Callback.register "c_nvec_cvode_ml_presolvefn" session_presolvefn;
          Callback.register "c_nvec_cvode_ml_jactimesfn" session_jactimesfn

  let proto_init lmm iter f (num_roots, roots) (num_eqs, y0) t0 =
    let cvode, errfile = external_init lmm iter y0 num_eqs num_roots t0 in
    let s = add_session cvode num_eqs num_roots errfile in
    Gc.finalise session_finalize s;
    s.rhsfn <- f;
    s.rootsfn <- roots;
    set_user_data s;
    s

  end

let init' = SessionTable.proto_init
let init lmm iter f roots n_y0 =
  SessionTable.proto_init lmm iter f roots n_y0 0.0

let nroots { nroots } = nroots
let neqs { neqs } = neqs

external reinit
    : 'a session -> float -> 'a nvector -> unit
    = "c_nvec_reinit"

external sv_tolerances  : 'a session -> float -> 'a nvector -> unit
    = "c_nvec_sv_tolerances"
external ss_tolerances  : 'a session -> float -> float -> unit
    = "c_ss_tolerances"
external wf_tolerances  : 'a session -> unit
    = "c_nvec_wf_tolerances"

let wf_tolerances s ferrw =
  s.errw <- ferrw;
  wf_tolerances s

external get_root_info  : 'a session -> Roots.t -> unit
    = "c_get_root_info"

external normal
    : 'a session -> float -> 'a nvector -> float * solver_result
    = "c_nvec_normal"

external one_step
    : 'a session -> float -> 'a nvector -> float * solver_result
    = "c_nvec_one_step"

external get_dky
    : 'a session -> float -> int -> 'a nvector -> unit
    = "c_nvec_get_dky"

external get_integrator_stats : 'a session -> integrator_stats
    = "c_get_integrator_stats"

external get_work_space         : 'a session -> int * int
    = "c_get_work_space"

external get_num_steps          : 'a session -> int
    = "c_get_num_steps"

external get_num_rhs_evals      : 'a session -> int
    = "c_get_num_rhs_evals"

external get_num_lin_solv_setups : 'a session -> int
    = "c_get_num_lin_solv_setups"

external get_num_err_test_fails : 'a session -> int
    = "c_get_num_err_test_fails"

external get_last_order         : 'a session -> int
    = "c_get_last_order"

external get_current_order      : 'a session -> int
    = "c_get_current_order"

external get_actual_init_step   : 'a session -> float
    = "c_get_actual_init_step"

external get_last_step          : 'a session -> float
    = "c_get_last_step"

external get_current_step       : 'a session -> float
    = "c_get_current_step"

external get_current_time       : 'a session -> float
    = "c_get_current_time"

let print_integrator_stats s =
  let stats = get_integrator_stats s
  in
    Printf.printf "num_steps = %d\n"           stats.num_steps;
    Printf.printf "num_rhs_evals = %d\n"       stats.num_rhs_evals;
    Printf.printf "num_lin_solv_setups = %d\n" stats.num_lin_solv_setups;
    Printf.printf "num_err_test_fails = %d\n"  stats.num_err_test_fails;
    Printf.printf "last_order = %d\n"          stats.last_order;
    Printf.printf "current_order = %d\n"       stats.current_order;
    Printf.printf "actual_init_step = %e\n"    stats.actual_init_step;
    Printf.printf "last_step = %e\n"           stats.last_step;
    Printf.printf "current_step = %e\n"        stats.current_step;
    Printf.printf "current_time = %e\n"        stats.current_time;

external set_error_file : 'a session -> string -> bool -> unit
    = "c_set_error_file"

external set_err_handler_fn  : 'a session -> unit
    = "c_nvec_set_err_handler_fn"

let set_err_handler_fn s ferrh =
  s.errh <- ferrh;
  set_err_handler_fn s

external clear_err_handler_fn  : 'a session -> unit
    = "c_nvec_clear_err_handler_fn"

let clear_err_handler_fn s =
  s.errh <- (fun _ -> ());
  clear_err_handler_fn s

external set_max_ord            : 'a session -> int -> unit
    = "c_set_max_ord"
external set_max_num_steps      : 'a session -> int -> unit
    = "c_set_max_num_steps"
external set_max_hnil_warns     : 'a session -> int -> unit
    = "c_set_max_hnil_warns"
external set_stab_lim_det       : 'a session -> bool -> unit
    = "c_set_stab_lim_det"
external set_init_step          : 'a session -> float -> unit
    = "c_set_init_step"
external set_min_step           : 'a session -> float -> unit
    = "c_set_min_step"
external set_max_step           : 'a session -> float -> unit
    = "c_set_max_step"
external set_stop_time          : 'a session -> float -> unit
    = "c_set_stop_time"
external set_max_err_test_fails : 'a session -> int -> unit
    = "c_set_max_err_test_fails"
external set_max_nonlin_iters   : 'a session -> int -> unit
    = "c_set_max_nonlin_iters"
external set_max_conv_fails     : 'a session -> int -> unit
    = "c_set_max_conv_fails"
external set_nonlin_conv_coef   : 'a session -> float -> unit
    = "c_set_nonlin_conv_coef"
external set_iter_type          : 'a session -> iter -> unit
    = "c_set_iter_type"

external set_root_direction'    : 'a session -> int_array -> unit
    = "c_set_root_direction"

let int_of_root_direction x =
  match x with
  | Increasing -> 1l
  | Decreasing -> -1l
  | IncreasingOrDecreasing -> 0l

let set_root_direction s rda =
  let n = nroots s in
  let rdirs = make_int_array n in
  if (n > Array.length rda)
    then Bigarray.Array1.fill rdirs
            (int_of_root_direction IncreasingOrDecreasing);
  Array.iteri (fun i v -> rdirs.{i} <- int_of_root_direction v) rda;
  set_root_direction' s rdirs

let set_all_root_directions s rd =
  let rdirs = make_int_array (nroots s) in
  Bigarray.Array1.fill rdirs (int_of_root_direction rd);
  set_root_direction' s rdirs

external set_no_inactive_root_warn      : 'a session -> unit
    = "c_set_no_inactive_root_warn"

external get_num_stab_lim_order_reds    : 'a session -> int
    = "c_get_num_stab_lim_order_reds"

external get_tol_scale_factor           : 'a session -> float
    = "c_get_tol_scale_factor"

external get_err_weights                : 'a session -> 'a nvector -> unit
    = "c_nvec_get_err_weights"

external get_est_local_errors           : 'a session -> 'a nvector -> unit
    = "c_nvec_get_est_local_errors"

external get_num_nonlin_solv_iters      : 'a session -> int
    = "c_get_num_nonlin_solv_iters"

external get_num_nonlin_solv_conv_fails : 'a session -> int
    = "c_get_num_nonlin_solv_conv_fails"

external get_num_g_evals                : 'a session -> int
    = "c_get_num_g_evals"

module Dls =
  struct
    external set_dense_jac_fn  : 'a session -> unit
        = "c_nvec_dls_set_dense_jac_fn"

    let set_dense_jac_fn s fjacfn =
      s.jacfn <- fjacfn;
      set_dense_jac_fn s

    external clear_dense_jac_fn : 'a session -> unit
        = "c_nvec_dls_clear_dense_jac_fn"

    let clear_dense_jac_fn s =
      s.jacfn <- (fun _ _ -> ());
      clear_dense_jac_fn s

    external set_band_jac_fn   : 'a session -> unit
        = "c_nvec_dls_set_band_jac_fn"

    let set_band_jac_fn s fbandjacfn =
      s.bandjacfn <- fbandjacfn;
      set_band_jac_fn s

    external clear_band_jac_fn : 'a session -> unit
        = "c_nvec_dls_clear_band_jac_fn"

    let clear_band_jac_fn s =
      s.bandjacfn <- (fun _ _ _ _ -> ());
      clear_band_jac_fn s

    external get_work_space : 'a session -> int * int
        = "c_dls_get_work_space"

    external get_num_jac_evals    : 'a session -> int
        = "c_dls_get_num_jac_evals"

    external get_num_rhs_evals    : 'a session -> int
        = "c_dls_get_num_rhs_evals"
  end

module Diag =
  struct
    external get_work_space       : 'a session -> int * int
        = "c_diag_get_work_space"

    external get_num_rhs_evals    : 'a session -> int
        = "c_diag_get_num_rhs_evals"
  end

module BandPrec =
  struct
    external get_work_space : 'a session -> int * int
        = "c_bandprec_get_work_space"

    external get_num_rhs_evals    : 'a session -> int
        = "c_bandprec_get_num_rhs_evals"
  end

module Spils =
  struct
    type 'a solve_arg = 'a callback_solve_arg =
      {
        rhs   : 'a;
        gamma : float;
        delta : float;
        left  : bool;
      }

    type gramschmidt_type =
      | ModifiedGS
      | ClassicalGS

    external set_preconditioner  : 'a session -> unit
        = "c_nvec_set_preconditioner"

    let set_preconditioner s fpresetupfn fpresolvefn =
      s.presetupfn <- fpresetupfn;
      s.presolvefn <- fpresolvefn;
      set_preconditioner s

    external set_jac_times_vec_fn : 'a session -> unit
        = "c_nvec_set_jac_times_vec_fn"

    let set_jac_times_vec_fn s fjactimesfn =
      s.jactimesfn <- fjactimesfn;
      set_jac_times_vec_fn s

    external clear_jac_times_vec_fn : 'a session -> unit
        = "c_nvec_clear_jac_times_vec_fn"

    let clear_jac_times_vec_fn s =
      s.jactimesfn <- (fun _ _ _ -> ());
      clear_jac_times_vec_fn s

    external set_prec_type : 'a session -> preconditioning_type -> unit
        = "c_set_prec_type"

    external set_gs_type : 'a session -> gramschmidt_type -> unit
        = "c_set_gs_type"

    external set_eps_lin            : 'a session -> float -> unit
        = "c_set_eps_lin"

    external set_maxl               : 'a session -> int -> unit
        = "c_set_maxl"

    external get_num_lin_iters      : 'a session -> int
        = "c_spils_get_num_lin_iters"

    external get_num_conv_fails     : 'a session -> int
        = "c_spils_get_num_conv_fails"

    external get_work_space         : 'a session -> int * int
        = "c_spils_get_work_space"

    external get_num_prec_evals     : 'a session -> int
        = "c_spils_get_num_prec_evals"

    external get_num_prec_solves    : 'a session -> int
        = "c_spils_get_num_prec_solves"

    external get_num_jtimes_evals   : 'a session -> int
        = "c_spils_get_num_jtimes_evals"

    external get_num_rhs_evals      : 'a session -> int
        = "c_spils_get_num_rhs_evals"

  end

