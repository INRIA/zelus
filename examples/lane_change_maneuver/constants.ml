(* Author: François Bidet *)

let dt = 0.05 (* print period in seconds *)
let dt_noise = 0.5 (* period of noise generation *)

let l = 2.7
let g = 9.81
let mu = 0.8
let b = 0.57 *. l
let a = l -. b
let j = 1.57 (* is equal to I_z /. m or J /. m *)
let c_f = -. 10.8
let c_r = -. 17.8

let pi = Float.pi

let v_min = 0.
let v_max = 150. /. 3.6
let alpha_min = -. 3.
let alpha_max = 2.
let delta_min = -. pi /. 4.
let delta_max = pi /. 4.
let v_des = 70. /. 3.6
let t_gap = 1.5
let t_gap_m = 1.
let gap = v_des *. t_gap
