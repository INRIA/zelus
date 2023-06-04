(* Uses Florent Monnier's OpenGL bindings for Ocaml:
 *   http://www.linux-nantes.org/~fmonnier/ocaml/GL/?p=home
 *)

open GL
open GLE
open Glu
open Glut

(*
 * ||                     ||
 * ||/\/\/\/\O   O/\/\/\/\||
 * ||                     ||
 * w1       p1   p2       w2
 *
 * w1 = right-hand edge of wall 1
 * p1 = right-hand edge of ball 1
 * w2 = left-hand edge of wall 2
 * p2 = left-hand edge of ball 2
 *
 *)

(* options *)
let update_period = 4

(* model parameters *)
let anglex = ref 0.0
let angley = ref 30.0
let anglez = ref 0.0

let wall_width       = 0.02
let wall_size        = 0.50

let spring_thickness = 0.01
let spring_ncoils    = 10.0
let spring_radius    = 0.10

let ball_radius = wall_size /. 3.0

let distance = 3.0
let resting_space = spring_thickness *. spring_ncoils +. (2.0 *. ball_radius)
let left_offset = -. distance /. 4.0
let w1 = 0.0 -. (wall_width /. 2.0) -. resting_space
let w2 = distance +. (wall_width /. 2.0) +. resting_space

(* display parameters *)

let lightOnePosition = (280.0, 100.0, 50.0, 0.0)
let lightAmbient = (0.5, 0.5, 0.5, 1.0)
let lightDiffuse = (0.2, 0.2, 0.2, 1.0)

(* communication of model state *)

let read_state fin =
  try
    let s = input_line fin in
    let i = String.index s ',' in
    let p1 = float_of_string (String.sub s 0 i) in
    let p2 = float_of_string (String.sub s (i + 1) (String.length s - i - 1)) in
    Some (p1, p2)
  with _ -> None

(* draw various elements of the model *)

let draw_wall xpos =
  glPushMatrix();
  glTranslate xpos 0.0 0.0;
  glScale wall_width wall_size wall_size;
  glutSolidCube 1.0;
  glPopMatrix()

let draw_floor () =
  glPushMatrix();
  glTranslate (distance /. 2.0) (-. wall_size /. 2.0) 0.0;
  glScale (w2 -. w1 +. wall_width) wall_width wall_size;
  glutSolidCube 1.0;
  glPopMatrix()

let draw_spring x1 x2 =
  let step_size = (x2 -. x1) /. spring_ncoils in
  let length_degrees = spring_ncoils *. 360.0 in
  glPushMatrix();
  glTranslate x1 0.0 0.0;
  glRotate 90.0 0.0 1.0 0.0;
  glScale 1.0 1.0 1.0;
  gleHelicoid spring_thickness spring_radius 0.0 0.0
              step_size None None 0.0 length_degrees;
  glPopMatrix()

let draw_ball x =
  glPushMatrix();
  glTranslate x 0.0 0.0;
  glScale 1.0 1.0 1.0;
  glutSolidSphere ball_radius 24 24;
  glPopMatrix()

let display p1 p2 () =
  glClear [GL_COLOR_BUFFER_BIT; GL_DEPTH_BUFFER_BIT];
  glLoadIdentity();

  glTranslate 0.0 0.0 (-. 2.5);

  glRotate (!angley) 1.0 0.0 0.0;
  glRotate (!anglex) 0.0 1.0 0.0;
  glRotate (!anglez) 0.0 0.0 1.0;

  glPushMatrix();
  glTranslate left_offset 0.0 0.0;

  glLight (GL_LIGHT 0) (Light.GL_POSITION lightOnePosition);

  glScale 0.5 0.5 0.5;

  glColor3 0.0 0.5 0.0;
  glMaterial GL_FRONT (Material.GL_AMBIENT (1.0, 1.0, 1.0, 1.0));
  draw_wall w1;
  draw_wall w2;
  draw_floor ();

  glMaterial GL_FRONT_AND_BACK (Material.GL_SHININESS 1.0);
  glColor3 0.8 0.8 0.8;
  draw_spring w1 (!p1 -. ball_radius *. 1.5);
  draw_spring w2 (!p2 +. ball_radius *. 1.5);

  glMaterial GL_FRONT (Material.GL_SPECULAR (0.0, 0.0, 0.0, 0.0));
  glColor3 1.0 0.0 0.0;
  draw_ball (!p1 -. ball_radius);
  glColor3 0.0 0.0 1.0;
  draw_ball (!p2 +. ball_radius);

  glPopMatrix();

  glutSwapBuffers()

(* initialisation and interface with glut *)

let make_model_functions p1i p2i fin =
  let p1 = ref p1i in
  let p2 = ref p2i in

  let rec update ~value:() =
    match read_state fin with
    | None -> schedule_update ()
    | Some (p1', p2') ->
        begin
          p1 := p1';
          p2 := p2';
          schedule_update ();
          glutPostRedisplay()
        end

  and schedule_update () =
    glutTimerFunc ~msecs:update_period ~timer:update ~value:()

  in
  (display p1 p2, update, schedule_update)

let reshape ~width:w ~height:h =
  glViewport 0 0 w h;
  glMatrixMode GL_PROJECTION;
  glLoadIdentity();
  let aspect = ((float w) /. (float (max 1 h))) in
  gluPerspective ~fovy:60.0 ~aspect ~zNear:0.5 ~zFar:100.0;
  glMatrixMode GL_MODELVIEW;
  glutPostRedisplay()

let keyboard ~key ~x ~y =
  match key with
  | 'q' | '\027' -> exit 0
  | _ -> ()

let special ~key ~x ~y =
  match key with
  | GLUT_KEY_LEFT  -> (anglex := !anglex -. 5.00; glutPostRedisplay())
  | GLUT_KEY_RIGHT -> (anglex := !anglex +. 5.00; glutPostRedisplay())
  | GLUT_KEY_UP    -> (angley := !angley -. 5.00; glutPostRedisplay())
  | GLUT_KEY_DOWN  -> (angley := !angley +. 5.00; glutPostRedisplay())
  | _ -> ()
          
let drag_scale = 0.3
let drag_last = ref (None : (int * int) option)

let mouse ~button ~state ~x ~y =
  match button, state with
  | GLUT_LEFT_BUTTON, GLUT_DOWN ->
      drag_last := Some (x, y)
  | GLUT_LEFT_BUTTON, GLUT_UP ->
      drag_last := None
  | _ -> ()

let motion ~x ~y =
  match !drag_last with
  | None -> ()
  | Some (xo, yo) ->
      anglex := !anglex +. (float (xo - x) *. drag_scale);
      angley := !angley +. (float (yo - y) *. drag_scale);
      drag_last := Some (x, y);
      glutPostRedisplay()

let gl_init () =
  glShadeModel GL_SMOOTH;
  glClearColor 0.0 0.0 0.3 0.0;
  glClearDepth 1.0;
  glEnable GL_DEPTH_TEST;

  gleSetJoinStyle [TUBE_NORM_EDGE; TUBE_JN_ANGLE; TUBE_JN_CAP];

  (* initialize lighting *)
  glLight (GL_LIGHT 0) (Light.GL_POSITION lightOnePosition);
  glLight (GL_LIGHT 0) (Light.GL_DIFFUSE  lightDiffuse);
  glLight (GL_LIGHT 0) (Light.GL_AMBIENT  lightAmbient);
  glEnable GL_LIGHT0;
  glEnable GL_LIGHTING;
  glColorMaterial GL_FRONT_AND_BACK GL_AMBIENT_AND_DIFFUSE;
  glEnable GL_COLOR_MATERIAL

let run_glut_loop p1i p2i fin =
  Random.self_init ();
  ignore(glutInit Sys.argv);

  glutInitDisplayMode [GLUT_RGB; GLUT_DOUBLE; GLUT_DEPTH]; (* dont use GLUT_DEPTH *)
  (*ignore(glutInitWindowSize 800 600);*)
  ignore(glutCreateWindow "Sticky Springs Visualisation");
  glutReshapeWindow ~width:800 ~height:600;

  (*glutFullScreen();*)
  glutSetCursor GLUT_CURSOR_CROSSHAIR;

  gl_init ();

  let (display, timer, start_timer) = make_model_functions p1i p2i fin in

  (* callbacks *)
  glutDisplayFunc  ~display;
  glutKeyboardFunc ~keyboard;
  glutSpecialFunc  ~special;
  glutReshapeFunc  ~reshape;
  glutMouseFunc    ~mouse;
  glutMotionFunc   ~motion;
  start_timer ();

  glutMainLoop()

let standalone () =
  Unix.set_nonblock Unix.stdin;
  run_glut_loop 0.0 distance stdin

(* To test, uncomment the line below, compile with:
 *
 *    ocamlc -o runworld unix.cma bigarray.cma
 *           -I +glMLite GL.cma GLE.cma Glu.cma Glut.cma
 *           world.ml
 *
 * and run:
 *    (echo "0.0,3.0"; sleep 2; echo "1.5,1.5") | ./runworld
 *)
(* let _ = standalone () *)

(* Fork a seperate process to run glut, communicate over a pipe *)

type t = out_channel

let create p1i p2i =
  let input, output = Unix.pipe () in
  let outch = Unix.out_channel_of_descr output in
  match Unix.fork () with
  | 0 -> (Unix.close input; outch) (* child *)
  | _ -> (* parent process *)
      begin
        Unix.close output;
        Unix.set_nonblock input;
        run_glut_loop p1i p2i (Unix.in_channel_of_descr input); (* Never returns *)
        outch
      end

let update fout p1 p2 =
  Printf.fprintf fout "%e,%e\n" p1 p2;
  flush fout

