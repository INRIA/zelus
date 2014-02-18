
val fuelc_period : float

val min_press : float
val max_press : float
val min_speed : int
val max_speed : int
val min_throt : int
val max_throt : int

val max_ego     : float
val zero_thresh : int
val hys         : int

val speed_vect : int array
val press_vect : float array
val throt_vect : int array

val press_est : float array array
val pump_con  : float array array
val speed_est : float array array
val throt_est : float array array

val ki : float
val ramp_rate_kix : Lookup.regular_int_breakpoints
val ramp_rate_kiy : Lookup.regular_float_breakpoints
val ramp_rate_kiz : float array array

val int_breakpoints   : (int array,   float, float) Lookup.breakpoint_lookup
val float_breakpoints : (float array, float, float) Lookup.breakpoint_lookup

val dump2d :
  string ->
  ('a, float, float) Lookup.breakpoint_lookup * 'a *
  (int -> 'a -> float * float * float) ->
  ('b, float, float) Lookup.breakpoint_lookup * 'b *
  (int -> 'b -> float * float * float) -> float array array -> unit

val dump_data : unit -> unit

