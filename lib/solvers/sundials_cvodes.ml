module Sens = Cvodes.Sensitivity
module RealArray = Sundials.RealArray

type t = Nvector_serial.kind Cvode.serial_session

type nvec = Nvector_serial.t
let cmake n = Nvector_serial.make n 0.0
let unvec = Nvector.unwrap

type sensmat = Nvector_serial.t array
let smake i j = Array.init i (fun _ -> Nvector_serial.make j 0.0)

let arrays_of_sensmat smat =
  Array.map (fun nvec ->
      let realarray = Nvector_serial.unwrap nvec in
      let n = Sundials.RealArray.length realarray in
      (* for some reason, the values in realarray are in the wrong order,
         this is a dirty fix for this issue *)
      Array.init n (fun i -> realarray.{n - i - 1})
  ) smat

type rhsfn = Zls.carray -> float -> Zls.carray -> Zls.carray -> unit
type dkyfn = nvec -> float -> int -> unit
type dkysensfn = sensmat -> float -> int -> unit

let initialize (f : rhsfn) params c uS0 =
  let s = Cvode.(init Adams Functional default_tolerances (f params) 0.0 c) in
  let np = Array.length uS0 in
  let pbar = RealArray.make np 1. in
  Sens.(init s EEtolerances Simultaneous
          ~sens_params:{ pvals = Some params; pbar = Some pbar; plist = None; }
          (AllAtOnce None) uS0);
  Sens.set_err_con s true;
  Sens.(set_dq_method s DQCentered 0.0);
  s

let reinitialize s t c uS0 =
  Cvode.reinit s t c;
  Sens.reinit s Simultaneous uS0

let step s tl c =
  fst (Cvode.solve_one_step s tl c)

let get_dky s c t k = Cvode.get_dky s c t k

(* get interpolated k-th derivatives of the sensitivity
   of state variable i at time t
   the state vector c is only used to get the number of state vectors to
   initialize uS properly *)
let get_sens_dky s uS t k = Sens.get_dky s uS t k

let set_stop_time s = Cvode.set_stop_time s
let set_min_step  s = Cvode.set_min_step s
let set_max_step  s = Cvode.set_max_step s
let set_tolerances s reltol abstol =
  Cvode.(set_tolerances s (SStolerances (reltol, abstol)))
