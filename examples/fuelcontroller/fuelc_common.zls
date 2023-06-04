
type fuel_mode = Low | Rich | Disabled

type sensor_values =
  { throttle : float;
    speed:     float;
    pressure:  float;
    ego:       float; }

let string_of_fuel_mode r = match r with
  | Low      -> "Low"
  | Rich     -> "Rich"
  | Disabled -> "Disabled"
  end

let int_breakpoints =
  Lookup.int_breakpoints ((Lookup.LinearLookup, true))

let float_breakpoints =
  Lookup.float_breakpoints ((Lookup.LinearLookup, true))

let speed_bps = (int_breakpoints,   Fuelc_data.speed_vect)
let throt_bps = (int_breakpoints,   Fuelc_data.throt_vect)
let press_bps = (float_breakpoints, Fuelc_data.press_vect)

let ramp_rate_kix_bps =
  (Lookup.regular_int_breakpoints_lookup, Fuelc_data.ramp_rate_kix)

let ramp_rate_kiy_bps =
  (Lookup.regular_float_breakpoints_lookup, Fuelc_data.ramp_rate_kiy)

let node lookup (x_table, y_table, r_table, (x, y)) =
  let rec lutable = (Mlmisc.make_lookup (x_table, y_table, r_table)) fby lutable
  in Mlmisc.use_lookup (lutable, (x, y))

