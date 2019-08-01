open Distribution

let () =
  Graphics.open_graph " 400x400";
  Graphics.auto_synchronize false

let clear () =
  Graphics.synchronize ();
  Graphics.clear_graph ()

let mouse_pos () =
  ignore (Graphics.wait_next_event [Graphics.Poll]);
  Graphics.mouse_pos ()

let draw_point color pos =
  begin match pos with
    | [ x ; y ] ->
      Graphics.set_color color;
      Graphics.draw_circle (int_of_float x) (int_of_float y) 2;
  | _ -> assert false
  end

let draw_obs color pos =
  begin match pos with
    | [ x ; y ] ->
      Graphics.set_color color;
      Graphics.fill_circle (int_of_float x) (int_of_float y) 8;
  | _ -> assert false
  end

let draw_point_dist dist =
  begin match dist with
  | Dist_sampler (_, _) -> assert false
  | Dist_support support ->
      (* List.iter *)
      (*   (fun (pos, prob) -> *)
      (*      let color = *)
      (*        let n = int_of_float (255. *. (1. -. max 0.4 prob)) in *)
      (*        if prob > 0.003 then Graphics.black *)
      (*        else Graphics.rgb n n n *)
      (*      in *)
      (*      draw_point color pos *)
      (*   ) support *)
      let support =
        List.sort (fun (_, prob1) (_, prob2) -> compare prob1 prob2) support
      in
      let len = 1 + (List.length support / 200) in
      let color = ref (List.length support / len + 1)  in
      List.iteri
        (fun i (pos, prob) ->
           if i mod len = 0 then decr color;
           draw_point (Graphics.rgb !color !color !color) pos)
        support
  | Dist_mixture _ -> assert false
  end

let () = Random.self_init()
let speed = [7.0; 7.0]
let p_noise = [5.0; 5.0]
let a_noise = [0.5; 0.5]
let p_init = [0.; 0.]

let observe_pos (x, y) =
  [ Distribution.draw (Distribution.gaussian (x, 5.));
    Distribution.draw (Distribution.gaussian (y, 5.)) ]

let observe_acc (x, y) =
  [ Distribution.draw (Distribution.gaussian (x, 0.01));
    Distribution.draw (Distribution.gaussian (y, 0.01)) ]

let ( +: ) a b = List.map2 (fun x y -> x +. y) a b
let ( -: ) a b = List.map2 (fun x y -> x -. y) a b
let ( *: ) a y = List.map (fun x -> x *. y) a
let norm a = sqrt (List.fold_left (fun acc x -> acc +. (x *. x)) 0. a)

let to_pair l =
  begin match l with
  | [ x; y; ] -> (x, y)
  | _ -> assert false
  end
