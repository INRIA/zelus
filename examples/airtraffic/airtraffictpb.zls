(*
 * This example is taken from the paper:
 *   "Conflict Resolution in Air Traffic Management; A Study in Multiagent
 *    Hybrid Systems", Tomlin, Pappas, Sastry, 1998
 *
 * It models a 'conflict resolution manouever' for two planes: Aircraft1 and
 * Aircraft2. Both aircraft are flying at a similar altitude and with constant
 * velocity and heading. Two zones are defined around each aircraft:
 *
 *           ***************
 *          *     alert     *
 *         *                 *
 *        *     *********     *
 *       *     *protected*     *
 *       *    *           *    *
 *       *    *    >->    *    *
 *       *    *           *    *
 *       *     *         *     *
 *        *     *********     *
 *         *                 *
 *          *               *
 *           ***************
 *
 * A 'conflict resolution manouever' is considered when two planes have entered
 * into each other's alert zones. The system aims to ensure that neither plane
 * ever * enters the other's protected zone.
 *
 * In the model, the position and heading of Aircraft1 define, respectively, the
 * origin and direction of the positive x-axis of a relative coordinate system,
 * in which the position of Aircraft2 is specified. The heading of Aircraft2 is
 * specified relative to the positive x-axis.
 *
 *                      .
 *                      .         (x_r, y_r) with heading theta_r
 *                      .      >2>
 *                      .
 *              . . . .>1>. . . .
 *                      .
 *                      .
 *                      .
 *                      .
 *
 * The initial condition in the model is that the aircraft are cruising outside
 * each other's protected zones, but inside each other's alert zones.
 *
 * The manouever modelled in this case is (taken directly from the paper):
 *
 * 1) "Cruise"
 *    cruise until aircraft are alpha1 miles apart.
 *
 * 2) "Left"
 *    Make a heading change of delta_phi and fly until a lateral displacement of
 *    at least d miles is acheived for both aircraft.
 *
 * 3) "Straight"
 *    Make a heading change to the original heading and fly until the aircraft
 *    are alpha2 miles apart.
 *
 * 4) "Right"
 *    Make a heading change of -delta_phi and fly until a lateral displacement
 *    of d miles is acheived for both aircraft.
 *
 * 5) "Cruise"
 *    Make a heading change to original heading and cruise.
 *
 * Note that, in the model at least, the heading changes occur simultaneously
 * and instantaneously.
 *
 *)

(** constants, initial state **)

let pi = 4.0 *. atan 1.0

let d = 10.0                (* distance to deviate for avoidance, in miles *)
let delta_phi = (pi /. 4.0) (* change in heading for avoidance, radians *)

let radius_protected = 5.0  (* radius of the protected zone, in miles *)
let radius_alert = 25.0     (* radius of the alert zone, in miles *)

let alpha1 = 16.0           (* distance at which avoidance is triggered *)
let alpha2 = 20.0           (* distance at which avoidance is terminated *)

let aircraft1_v = 540.0   (* velocity of aircraft1, miles/hour *)
let aircraft2_v = 570.0   (* velocity of aircraft2, miles/hour *)

(* initial position of aircraft2, relative to aircraft1 *)
let aircraft2_xi = 60.0
let aircraft2_yi = 28.0
let aircraft2_thetai = -. 3.0 *. pi /. 4.0

(** algorithm **)

let rotate (theta, x, y) = (x', y') where
  rec cos_theta = cos(theta)
  and sin_theta = sin(theta)
  and x' = (cos_theta *. x) +. (-. sin_theta *. y)
  and y' = (sin_theta *. x) +. (cos_theta *. y)

let sqr x = x *. x

let hybrid integr(x', x0) = x where rec der x = x' init x0

let hybrid avoidance (x_i, y_i, theta_i, v_1, v_2) = (st, x, y, theta, t) where
  rec theta = theta_i
  and init t = 0.0
  and automaton
      | Start ->
          do
                der x = 0.0 init x_i
            and der y = 0.0 init y_i
            and st = -1
          until (init on true) then Cruise(x,y)
          done

      | Cruise(x0, y0) ->
          local nx0, ny0 in
          do
                der x = x' init x0
            and der y = y' init y0
            and st = 0
            and (nx0, ny0) = rotate(-. delta_phi, x, y)
          until (up(sqr(alpha1) -. sqr(x) -. sqr(y))) then Left(nx0, ny0)
          done

      | Left(x0, y0) ->
          local nx0, ny0, t1, t2 in
          do
                der t = 1.0
            and t1 = d /. (v_1 *. sin(delta_phi))
            and t2 = d /. (v_2 *. sin(delta_phi))
            and der x = x' init x0
            and der y = y' init y0
            and st = 1
            and (nx0, ny0) = rotate(delta_phi, x, y)
          until (up(t -. max(t1, t2))) then Straight(nx0, ny0)
          done

      | Straight(x0, y0) ->
          local nx0, ny0 in
          do
                der x = x' init x0
            and der y = y' init y0
            and st = 2
            and (nx0, ny0) = rotate(delta_phi, x, y)
          until (up(sqr(x) +. sqr(y) -. sqr(alpha2))) then Right(nx0, ny0)
          done

      | Right(x0, y0) ->
          local nx0, ny0 in
          do
                der t = -. 1.0
            and der x = x' init x0
            and der y = y' init y0
            and st = 3
            and (nx0, ny0) = rotate(-. delta_phi, x, y)
          until (up(-. t)) then Cruise(nx0, ny0)
          done
      end
  and x' = -. v_1 +. v_2 *. cos(theta)
  and y' = v_2 *. sin(theta)

let hybrid noavoidance (x_i, y_i, theta_i, v_1, v_2) = (st, x, y, theta, t) where
  rec theta = theta_i
  and der x = -. v_1 +. v_2 *. cos(theta) init x_i
  and der y = v_2 *. sin(theta) init y_i
  and init st = 0
  and t = 0.0

(** Animation **)

open Airtrafficgui

let hybrid main () = () where
  rec () = showupdate (d, delta_phi, radius_alert, radius_protected, delta_phi,
                       st, xr, yr, theta_r, aircraft1_v, aircraft2_v, t)
    every period (0.001) init ()
  and (st, xr, yr, theta_r, t) =
    avoidance (aircraft2_xi, aircraft2_yi, aircraft2_thetai,
               aircraft1_v, aircraft2_v)

  (*
    (let rec win = (show (d, delta_phi, radius_alert, radius_protected)) fby win
     in update (win, xr, yr, theta_r, aircraft1_v, aircraft2_v, t))
    every period (0.1) init ()
  *)
