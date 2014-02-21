(********************
n.IV in simulink-stateflow-automotive.pdf
Car suspension system
Cyprien L. 25/05/2012
*******************)

(* Physial constants *)
let l_f = 0.9     (* Horizontal dist. from body center of gravity 
                     to front suspension *)
let l_r = 1.2     (* Horizontal dist. from body center of gravity 
                     to rear suspension *)
let m_b = 1200.0  (* Body mass *)
let i_yy = 2100.0 (* Body moment of inertia about center of gravity *)
let k_f = 28000.0 (* Front suspension spring rate *)
let k_r = 21000.0 (* Rear suspension spring rate *)
let c_f = 2500.0  (* Front suspension damper rate *)
let c_r = 2000.0  (* Rear suspension damper rate *)
let g = 9.81      (* Gravity *)

(* One spring/Damper suspension *)
(* [theta, theta_dot] : pitch (rotational) angle and rate of change *)
(* [z,z_dot] : bounce (vertical) distance and velocity *)
(* [k,c] : suspension spring rate and damping rate at each wheel*)
(* [l] : horizontal distance from body center of gravity to suspension *)
let suspension(theta,theta_dot,z,z_dot,k,c,l) = force, pitch_moment where
  rec force = 2.0 *. k *. (l*.theta -. z) +. 2.0 *. c *. (l *. theta_dot -. z_dot)
  and pitch_moment = -.l *. force

(* The car : *)
(* [h]: floor height *)
(* [m_y]: torque due to the car acceleration *)
let hybrid car(h,m_y) = theta,theta_dot,z,z_dot,f_front  where
  rec der z_dot = (f_front +. f_rear -. m_b*.g) /. m_b init 0.0
  and der z_rel = z_dot init 0.0
  and z = z_rel +. h
  and der theta_dot = (m_front +. m_rear +. m_y) /. i_yy init 0.0
  and der theta = theta_dot init 0.0
  and f_front,m_front = suspension(theta,theta_dot,z,z_dot,k_f,c_f,l_f)
  and f_rear,m_rear = suspension(theta,theta_dot,z,z_dot,k_r,c_r,-.l_r)

let hybrid main () =
  let der t = 1.0 init 0.0 in

(* The inputs *)
(* road height *)
  let h = present (period(10.0)) -> 0.0
    | (period 5.0(10.0)) -> 0.01 init 0.0 in
(* Moment due to vehcle accel/decel *)
  let y = present (period(10.0)) -> 0.0
    | (period 3.0(10.0)) -> 100.0 init 0.0 in

(* The Car *)  
  let theta,theta_dot,z,z_dot,f_front = car(h,y) in

(* Plot variables *)
  present (period(0.05)) ->
    let hplot = Scope.scope(-.0.05,0.15,
                            ("Road height", Scope.linear, h)) in
    let yplot = Scope.scope(-1.0,105.0,
                            ("Moment due to vehicle accel/decel", Scope.linear, y)) in
    let outs = Scope.scope2(-1.0,10.0,
                            ("theta", Scope.linear, theta),
                            ("z", Scope.linear, z)) in
    let fplot = Scope.scope(6000.0,7000.0,
                            ("Reaction force at front wheel", Scope.linear, f_front )) in
    let thetadotplot = Scope.scope(-0.05, 0.05,
                            ("thetadot", Scope.linear, theta_dot)) in
    let zdotplot = Scope.scope(-0.1,0.1,
                            ("Zdot", Scope.linear, z_dot)) in
    Scope.window5 ("suspension", 30.0, t, thetadotplot,zdotplot,fplot,hplot, yplot)
  else ()
