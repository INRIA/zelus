(** Vector lib **)

type vect =
    { x: float;
      y: float; }

let vzero =
  { x = 0.;
    y = 0.; }

let vone =
  { x = 1.;
    y = 1.; }

let vplus v1 v2 =
  { x = v1.x +. v2.x;
    y = v1.y +. v2.y; }
let (+:) = vplus

let vminus v1 v2 =
  { x = v1.x -. v2.x;
    y = v1.y -. v2.y; }
let ( -: ) = vminus

let vscale a v =
  { x = a *. v.x;
    y = a *. v.y; }
let ( *: ) = vscale
let ( /: ) = fun v a -> vscale (1. /. a) v

let vmult v1 v2 =
  { x = v1.x *. v2.x;
    y = v1.y *. v2.y; }
let ( **: ) = vmult

let vnorm v =
  let m = v **: v in
  sqrt (m.x +. m.y)

let vnormalize v =
  if v = vzero then vzero
  else v /: (vnorm v)

let vcos v1 v2 =
  let n1 = sqrt (vnorm v1) in
  let n2 = sqrt (vnorm v2) in
  (v1.x *. v2.x +. v1.y *. v2.y) /. (n1 *. n2)

let vrandom xmax ymax =
  { x = Random.float xmax;
    y = Random.float ymax; }

let vrandom_sphere center radius =
  let n = Random.float radius in
  let a = Random.float (2. *. 3.14) in
  vrandom (n *. cos a) (n *. sin a)

let vmouse () =
  let x, y = Graphics.mouse_pos () in
  { x = (float) x;
    y = (float) y; }

let vprint v =
  print_endline
    ("("^(string_of_float v.x)^","^(string_of_float v.y)^")")

(** Utils **)

let barycenter n b v =
  let b = (v +: ((float) n) *: b) /: ((float) (n + 1)) in
  b, n + 1

let damping limit v =
  let n = vnorm v in
  if n > limit then (limit /. n) *: v
  else v

(** Parameters **)

let boids_number = 500
let family_number = 3
let speed_limit = 2.
let acceleration_limit = 0.5
let vision_angle = -0.9
let repulsion_distance = 50.
let separation_distance = 10.
let alignment_distance = 50.
let cohesion_distance = 100.
let repulsion_force = 1000.
let separation_force = 100.0
let cohesion_force = 0.1
let alignment_force = 5.0
let selfishness = 0.6
let dt = 1.
type bounds = { xmin: float; xmax: float;
		ymin: float; ymax: float }
let bounds = { xmin = 0.; xmax = 600.; ymin = 0.; ymax = 600. }
	       
type boid =
    { id: int;
      family: int;
      position: vect;
      speed: vect;
      acceleration: vect }
