(********************
Ball bouncing on a spring (with damping)
Cyprien L. 2/05/2012

   / \
   \ /


___________
| |    /
|||    \
 |     /
 |     \

*******************)

open Graphics
let start = 
  open_graph "";
  auto_synchronize false;
  set_line_width 4

(**Graphical features **)
(* [z]: ball height *)
(* [z_plateform]: plateform height *)
(* [rad]: ball radius *)
let discrete draw_ball_plateform(z,z_plateform,rad) = 
  clear_graph ();
  let z = truncate z in
  let z_plateform = truncate z_plateform in
  draw_circle (100, z, truncate(rad));
  moveto(0,z_plateform);
  lineto(400,z_plateform);
  synchronize ()

(*physical constants for the ball*)
let g = 9.81
let m_ball = 80.0
let radius = 20.0
(*and for the plateform*)
let m_plateform = 10.0
let k = 200.0
let f = 5.0 (* damping *)
let base_level = 100.0
let f_scratch = 1.0 (* level of interaction when sticked *)

let hybrid integr(x', i) = x where der x = x' init i

(* Hybrid system description *)
(* [z0]: initial level of the ball *)
(* [v0]: initial level of the plateform *)
(* [radius]: ball radius *)
let hybrid system(z0,v0,radius) = (z,z_plateform) where
  rec automaton
      | Fall(z_init,v_init,z_p_init,v_p_init) -> 
          do der z = v init z_init
          and der v = -.g init v_init
          and der z_plateform = v_plateform init z_p_init
          and der v_plateform = 
            -.(k/.m_plateform)*.(z_plateform-. base_level) 
              -. (f/.m_plateform)*.v_plateform init v_p_init
          until (up(-.z+.z_plateform+.radius)) then
            Sticked(z_plateform,((m_ball *. v +. m_plateform *. v_plateform) 
                 /.(m_ball +. m_plateform)))
      | Sticked(z_init,v_init) -> local a_plateform in
        do a_plateform =  -.(k/.(m_plateform+.m_ball)) *. (z_plateform -. 100.0)
            -. (f/.(m_plateform+.m_ball)) *. v_plateform
          and der z = v_plateform init (z_init+.radius)
          and der v = a_plateform init v_init
          and der z_plateform = v_plateform init z_init
          and der v_plateform = a_plateform init v_init
          until 
            (up(-.(m_ball *. (-.(k /. (m_plateform +. m_ball)) *. 
                                 (z_plateform-.100.0) 
                               -. (f /. (m_plateform +. m_ball)) 
                               *. v_plateform +. f_scratch))))
          then Fall(z, (m_ball/.(m_ball +. m_plateform)) *. v, z_plateform, (m_plateform/.(m_ball +. m_plateform))*. v_plateform)
      init Fall(z0,v0,base_level,5.0)

let hybrid main () =
  let t = period(0.2) in
  let (z,z_plateform) = system(400.0,30.0,radius) in
  (present t -> draw_ball_plateform(z,z_plateform,radius));
  ()
