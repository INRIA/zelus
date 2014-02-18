
open Fuelc_engine
open Fuelc_subsys
open Fuelc_common
open Library

(* Fuelc_common.fuelc_period should be a multiple of this value. *)
let fixedstep_period = 0.001

(* TODO: Do we still need this? *)
let fuelc_rate = max 1 (truncate (fuelc_period /. fixedstep_period))

(* Test: feed the engine model with values logged from Simulink *)
let hybrid test_engine_only () =
  let throttle_signal = zigzag (4.0, 5.0) +. 15.0
  and (o2_out, map, air_fuel_ratio) =
    engine_gas_dynamics (300.0, throttle_signal, fuel_rate)
  and fuel_rate = read_floats "fuel.in" every p init 0.0 in
            (* TODO: shouldn't need init if p is present initially *)
  and p = period 0.0 (0.001) (* TODO: make true initially *)
  and der t = 1.0 init 0.0
  in
  Mlmisc.print_floats_4 (t, o2_out, map, air_fuel_ratio)

(* Test: feed the discrete controller with values logged from Simulink *)
let hybrid test_controller_only () = () where
  let rec der t = 1.0 init 0.0
  and p = period 0.0 (0.001) (* TODO: make true initially *)
  (let
   rec air_fuel_ratio = read_floats "airfuel.in"
   and o2_out         = read_floats "o2out.in"
   and map            = read_floats "map.in"
   and sensor_values  = {throttle=read_floats "throttle.in";
                         speed=300.0;
                         ego=o2_out;
                         pressure=map}
   and fuel_rate = Fuelc_subsys.fuel_rate_control (sensor_values)
   in Mlmisc.print_floats_2 (t, fuelc_rate)) every p init 0.0

let engine_gas_dynamics_and_throttle ()
  =

  let stage1 () =
    seq
      (source throttle_signal)
      (pure
        (fun (throttle,
                ((sw_engspeed, sw_throt, sw_speed, sw_ego, sw_map), fuel_rate))
         -> (((if sw_engspeed then 300.0 else 700.0), throttle, fuel_rate),
             ((if sw_throt then throttle else 0.0),
              sw_speed,
              (if sw_engspeed then 300.0 else 700.0),
              sw_ego,
              sw_map,
              fuel_rate))))

  and stage2 () =
    pure
      (fun ((o2_out, map, air_fuel_ratio),
            (throttle, sw_speed, speed, sw_ego, sw_map, fuel_rate))
       -> (
        (air_fuel_ratio, o2_out, map,
        {throttle=throttle;
         speed=;
         ego=(if sw_ego then o2_out else 12.0);
         pressure=(if sw_map then map else 0.0)}
       )))
  in
  (seq
    (stage1 ())
    (seq
      (first (engine_gas_dynamics ()))
      (stage2 ())))


let hybrid simulation (sw_engspeed, sw_throt, sw_speed, sw_ego, sw_map)
  = (t, fuel_rate, o2_out, map, air_fuel_ratio)
  where
  rec der t = 1.0 init 0.0

  and throttle_angle = zigzag (4.0, 5.0) +. 15.0
  and throttle = if sw_throt    then throttle_angle else   0.0
  and engspeed = if sw_engspeed then 300.0          else 700.0
  and speed    = if sw_speed    then engspeed       else   0.0
  and ego      = if sw_ego      then o2_out         else  12.0
  and pressure = if sw_map      then map            else   0.0

  and fuelc_clk = period (0.01)
  and sensors   = {throttle=throttle; speed=speed; ego=ego; pressure=pressure}
  and fuel_rate = fuel_rate_controller (sensors) every fuelc_clk
                  init 1.209028005600

  and (o2_out, map, air_fuel_ratio) =
        engine_gas_dynamics (engspeed, throttle_angle, fuel_rate)

let sensors_baseline () =
  let sw_engine =   true
  and sw_throttle = true
  and sw_speed =    true
  and sw_ego =      true
  and sw_map =      true
  in
  (sw_engine, sw_throttle, sw_speed, sw_ego, sw_map)

let node failat n =
  not (after (truncate (n /. fixedstep_period)) true)

let node sensors_mapfail () =
  let sw_engine =   true
  and sw_throttle = true
  and sw_speed =    true
  and sw_ego =      true
  and sw_map =      not (square_pulse 5000 9000)
  in
  (sw_engine, sw_throttle, sw_speed, sw_ego, sw_map)

(* TODO: add plotting *)
let hybrid basic_fuel () =
  let (t, fuelc_rate, o2_out, map, air_fuel_ratio) =
    simulation (sensors_baseline ()) in
  Mlmisc.print_floats5 (t, o2_out, map, air_fuel_ratio, fuelc_rate)

(* TODO: add plotting *)
let node mapfail () =
  let rec sensors = sensors_mapfail () every (period 0.01)
                    init sensors_baseline ()
  and (t, fuelc_rate, o2_out, map, air_fuel_ratio) = simulation (sensors) in
  Mlmisc.print_floats5 (t, o2_out, map, air_fuel_ratio, fuelc_rate)

(* TODO: interactive control for switches, plotter to function like the one in
         Simulink, i.e. fixed period to show the same curve *)

