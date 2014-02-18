
open Solvers

let printf = Printf.printf

(* Detect zero-crossings during fixed-step solution. *)
module FixedstepZeroc : ZEROC_SOLVER =
  struct (* {{{ *)
    include ZerosInfrastructure

    type 'cvec t = {
        g : float -> 'cvec -> zxvec -> unit;
        mutable bothf_valid : bool;

        mutable f0 : zxvec;
        mutable f1 : zxvec;
        mutable t  : float;

        mutable roots : zvec;
        mutable calc_zc : float -> float -> int
      }

    let reinit ({ g; f1 } as s) t c =
      g t c f1;   (* fill f1, because it is immediately copied into f0 *)
      s.bothf_valid <- false

    let init (nroots, g) c =
      let s =
        {
            g = g;
            bothf_valid = false;

            f0 = create nroots;
            f1 = create nroots;
            t  = 0.0;

            roots = zvec_create nroots;
            calc_zc = get_check_root Up;
        }
      in
      reinit s 0.0 c;
      s

    let num_roots { f0 } = length f0

    let set_root_directions s rd = (s.calc_zc <- get_check_root rd)

    let roots { roots } = roots

    (* f0/t0 take the previous values of f1/t1, f1/t1 are refreshed by g *)
    let next_mesh ({ g; f0 = f0; f1 = f1; roots } as s) t c =

      (* swap f0 and f1; f0 takes the previous value of f1 *)
      s.f0 <- f1;
      s.f1 <- f0;
      s.t  <- t;

      (* calculate a new value for f1 *)
      g t c s.f1;
      s.bothf_valid <- true

    let find ({ g = g; bothf_valid = bothf_valid; f0 = f0; f1 = f1; t = t;
                roots = roots; calc_zc = calc_zc } as s) dky c =
      if not bothf_valid then None
      else if update_roots calc_zc f0 f1 roots then
        (if !debug then (printf "z| zero-crossing(s) found:\n";
                        log_limits f0 f1);
         s.bothf_valid <- false; Some t)
      else None

  end (* }}} *)

module type FIXED_STEP_SOLVER =
  sig
    include SOLVER
    val set_step_size : float -> unit
  end

(* A fixed step solver must be configured before use:
   - call set_horizon_step to set the step size
   - usually also call set_min_step
 *)
module Make (State : STATE_SOLVER) =
  struct
    include Solver (struct include State let step = full_step end)
                   (FixedstepZeroc)

    let step_size = ref 1.0
    let set_step_size s = (step_size := s)

    let init f ng c =
      let s = init f ng c in
      set_horizon_step s !step_size;
      s

  end

let register name doc m =
  let module NewModule = Make ((val m: STATE_SOLVER)) in
  let arg = ("-" ^ name,
             Arg.Float NewModule.set_step_size,
             "<stepsize> " ^ doc) in
  Zlsolve.register' name arg (module NewModule : SOLVER)

