
let pi = 4.0 *. atan 1.0

type component =
  { color     : GDraw.color;
    fill      : GDraw.color option;
    linewidth : int;
    points    : (int * int) list; }

type system =
  { components : component list;
    lower : int * int;
    upper : int * int;
    pivot : int * int;
    scale : int;
  }

let draw_component
  scale (xpivot, ypivot) angle (xoff, yoff) (d : GDraw.drawable) =

  let scale = float(scale) in

  let transform (x, y) =
    let x' = float(x - xpivot)
    and y' = float(y - ypivot) in
    let xr = x' *. cos(angle) -. y' *. sin(angle)
    and yr = x' *. sin(angle) +. y' *. cos(angle) in
    let x' = truncate (xr /. scale) + xoff
    and y' = truncate (yr /. scale) + yoff in
    x', y' in

  let draw { color; fill; linewidth; points } =
    let coords = List.map transform points in
    d#set_line_attributes ~width:linewidth ();
    (match fill with
     | None -> ()
     | Some c -> begin
         d#set_foreground c;
         d#polygon ~filled:true coords
     end);
    d#set_foreground color;
    d#polygon ~filled:false coords
    in

  draw

let scale { scale } = scale
let rescale sys scale = { sys with scale = scale }

let draw { pivot; scale; components } d angle offset =
  ignore (List.map (draw_component scale pivot angle offset d) components)

