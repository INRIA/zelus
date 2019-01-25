open Infer
open Distribution

let pi = 3.14

type motion_type = Stationary | Walking | Running

type walker = {
    position : float * float;
    velocity : float * float;
    motion_type : motion_type;
  }

let pos_noise = 0.01

let coast (prob, (dt, w)) =
  let std_dev = sqrt dt *. pos_noise in
  let { position = (x, y); velocity = (vx, vy) } = w in
  let (x', y') = (x +. dt *. vx, y +. dt *. vy)  in
  let x'' = sample (prob, gaussian x' std_dev) in
  let y'' = sample (prob, gaussian y' std_dev) in
  { w with position = (x'', y'') }

(* half lives of changing the motion type, in seconds *)
(* sometimes, we change to ourselves, to change direction *)
let motion_type_transition mt =
  begin match mt with
  | Stationary -> [(30., Walking); (60. *. 5., Running)]
  | Walking -> [(1., Walking); (10., Stationary); (60., Running)]
  | Running -> [(0.5, Running); (2., Walking)]
  end

let init_velocity (prob, mt) =
  let speed_at_random_direction speed =
    let angle = sample (prob, uniform_float 0. (2. *. pi)) in
    (speed *. cos angle, speed *. sin angle)
  in
  begin match mt with
  | Stationary -> (0., 0.)
  | Walking ->
      let speed = sample (prob, uniform_float 0. 2.) in
      speed_at_random_direction speed
  | Running ->
      let speed = sample (prob, uniform_float 2. 7.) in
      speed_at_random_direction speed
  end

(* default units are seconds *)
(* motion :: Double -> Walker -> RVar Walker *)
let rec motion (prob, (dt, w)) =
  let trans_lam =
    List.map
      (fun (t, mt) -> log 2. /. t, mt)
      (motion_type_transition w.motion_type)
  in
  let st =
    List.fold_left (fun acc (t, mt) -> acc +. t) 0. trans_lam
  in
  let t_transition = sample (prob, exponential st) in
  if t_transition > dt then coast (prob, (dt, w))
  else
    let w' = coast (prob, (t_transition, w)) in
    let mt = sample (prob, weighted_list trans_lam) in
    let vel = init_velocity (prob, mt) in
    motion (prob,
            (dt -. t_transition, { w' with velocity = vel; motion_type = mt }))

let real_motion (dt, w) =
  motion ((), (dt, w))

let position_std_dev = 10.

(* walkerMeasure :: Walker -> (Double, Double) -> PProg a () *)
let walker_measure (prob, (w, (mx, my))) =
  let (x, y) = w.position in
  factor (prob, score (gaussian x position_std_dev) mx);
  factor (prob, score (gaussian y position_std_dev) my)

(* walkerGenMeasurement :: Walker -> RVar (Double, Double) *)
let walker_gen_measurement w =
  let (x, y) = w.position in
  let mx = draw (gaussian x position_std_dev) in
  let my = draw (gaussian y position_std_dev) in
  (mx, my)

(* walkerStep :: Double -> (Double, Double) -> Walker -> PProg a Walker *)
let walker_step (prob, (dt, measured_position, w)) =
  let w' = motion (prob, (dt, w)) in
  walker_measure (prob, (w', measured_position));
  w'

(* walkerInit :: RVar Walker *)
let walker_init (prob, ()) =
  let mt =
    sample (prob,
            weighted_list [(0.7, Stationary); (0.25, Walking); (0.05, Running)])
  in
  let vel = init_velocity (prob, mt) in
  { position = (0., 0.); velocity = vel; motion_type = mt }

let real_walker_init () =
  walker_init ((), ())

let print_mt_dist mt_dist =
  begin match mt_dist with
  | Dist_support sup ->
      Format.printf "([";
      Format.pp_print_list
        ~pp_sep:(fun fmt () -> Format.fprintf fmt ",")
        (fun fmt (mt, p) ->
           begin match mt with
             | Stationary -> Format.fprintf fmt "(%f, Stationary)" p
             | Walking -> Format.fprintf fmt "(%f, Walking)" p
             | Running -> Format.fprintf fmt "(%f, Running)" p
           end)
        Format.std_formatter
        sup;
      Format.printf "])"
  | Dist_sampler _ -> assert false
  end

let print_pos_dist pos_dist =
  let x_dist, y_dist = Distribution.split pos_dist in
  Format.printf " (%f, %f)" (mean_float x_dist) (mean_float y_dist)

let print dist =
  let mt_dist, pos_dist = Distribution.split dist in
  print_mt_dist mt_dist;
  print_pos_dist pos_dist;
  Format.printf "@."

