(********************
Pong
Cyprien L. 14/05/2012
*******************)

open Graphics
let start = 
  open_graph "";
  auto_synchronize false;
  set_line_width 2

(** Common functions **)
let hybrid timer v = t where
  rec der c = 1.0 init -.v reset t -> -.v
  and t = up(last c)

type side = Right | Left

(**graphical features **)
let node draw_paddle(side,y,width) = 
  let y = truncate y in
  let x = if side = Left then 10 else size_x()-10 in
  moveto(x,y-(width/2));
  lineto(x,y+(width/2))

let node draw_ball(x,y,radius) = 
  draw_circle (x, y, truncate(radius))

let node draw_all(y_left,y_right,x_ball,y_ball,paddle_width) =
  clear_graph ();
  draw_paddle(Right,y_right,truncate paddle_width);
  draw_paddle(Left,y_left,truncate paddle_width);
  draw_ball(truncate x_ball,truncate y_ball,5.0);
  moveto(10,10);
  draw_string("x:" ^ string_of_int (truncate x_ball) ^ " y:" ^
              string_of_int (truncate y_ball));
  moveto(10,0);
  draw_string("left:" ^ string_of_float y_left ^ 
              " yright:" ^ string_of_float y_right);
  synchronize ()

(** Hybrid system description **)
(*ball*)
let g = 9.81
let m_ball = 80.0
(*paddle*)
let paddle_width = 40.0

let hybrid ball (y_leftpaddle,y_rightpaddle,paddle_width) = (x,y) where
  rec automaton
    Init -> 
      do der x = 0.0 init 100.0 
      and der y = 0.0 init 100.0
      until (period(1.0)) then Free(100.0, 100.0, 40.0, 10.0)
    | Free(x0,y0,v0x,v0y) -> 
        do der x = v_x init x0 
        and der v_x = 0.0 init v0x 
        and der y = v_y init y0 
        and der v_y = 0.0 init v0y (* g ? *) 
      until
            (up(y-.float_of_int(size_y()))) 
          (* up border *)  then Free(x,y,v_x,-.v_y) 
       else (up(-.y))  
          (* bottom border *)  then Free(x,y,v_x,-.v_y)  
       else (up(x-.float_of_int(size_x())+.10.0)
              on ((y < y_rightpaddle +. paddle_width)
                  && (y > y_rightpaddle-.paddle_width))) 
          (* right border on paddle*)
        then Free(x,y,-.v_x,v_y) 
       else (up(x-.float_of_int(size_x())+.10.0)
              on ((y >= y_rightpaddle +. paddle_width)
                  || (y <= y_rightpaddle-.paddle_width)))
          (* right border - out of paddle*)
        then Loose
       else (up(-.(x-.10.0))
              on ((y < y_leftpaddle+.paddle_width)
                  && (y > y_leftpaddle-.paddle_width)))
          (* left border on paddle*)
        then Free(x,y,-.v_x,v_y)
       else (up(-.(x-.10.0))
              on ((y >= y_leftpaddle+.paddle_width)
                  || (y <= y_leftpaddle-.paddle_width)))
        then Loose
     | Loose -> 
        do der x = 0.0 init float_of_int(size_x()/2) 
        and der y = 0.0 init float_of_int(size_y()/2) 
        done
  
let step = 0.1
let hybrid main () =
  let mousex,mousey = mouse_pos() in
  let t = timer step in

  let rec y_leftpaddle = present t -> 0.0 -> last y init float_of_int(size_x()/2)
  and y_rightpaddle = float_of_int mousey
  and (x,y) = ball(y_leftpaddle,y_rightpaddle, paddle_width) in
  
  draw_all(y_leftpaddle,y_rightpaddle, x, y,paddle_width)
