let robot_radius = 20
let scale_x = 300.
let scale_y = 300.
let offset_x = 200.
let offset_y = 200.

let scale_coord_x x = (truncate (x*.scale_x+.offset_x))
let scale_coord_y y = (truncate (y*.scale_y+.offset_y))
let start () =
  Graphics.open_graph "";
  Graphics.resize_window 800 600;
  Graphics.clear_graph ()

let show_robot x x_last y y_last angle= 
  Graphics.set_color Graphics.white;
  Graphics.fill_circle (scale_coord_x x_last) (scale_coord_y y_last) robot_radius;
  
  Graphics.set_color Graphics.red;
  Graphics.fill_circle (scale_coord_x x) (scale_coord_y y) robot_radius;
  Graphics.set_color Graphics.white;
  Graphics.fill_circle (scale_coord_x (x+. 0.03*.cos(angle)))
  (scale_coord_y (y+. 0.03*.sin(angle)))
  (truncate ((float_of_int robot_radius) *. 0.3))

let () = start ()