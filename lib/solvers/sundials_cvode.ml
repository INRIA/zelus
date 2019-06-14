
type t = Nvector_serial.kind Cvode.serial_session

type nvec = Nvector_serial.t
let cmake n = Nvector_serial.make n 0.0
let unvec = Nvector.unwrap

type rhsfn = float -> Zls.carray -> Zls.carray -> unit
type dkyfn = nvec -> float -> int -> unit
     
let initialize (f : rhsfn) c =
  Cvode.init Cvode.Adams Cvode.Functional Cvode.default_tolerances f 0.0 c

let reinitialize s t c =
  Cvode.reinit s t c

let step s tl c =
  fst (Cvode.solve_one_step s tl c)

let get_dky s c t k = Cvode.get_dky s c t k

let set_stop_time  = Cvode.set_stop_time
let set_min_step   = Cvode.set_min_step
let set_max_step   = Cvode.set_max_step
let set_tolerances s reltol abstol =
  Cvode.set_tolerances s (Cvode.SStolerances (reltol, abstol))

