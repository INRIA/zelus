type option =
  | Opt_no_reverse

type action = L | R | U | D

type loc = int * int

type 'a feature =
  | Wall
  | Empty
  | Value of 'a

type 'a map =
  { feature : (loc -> 'a feature);
    x_lim : int;
    y_lim : int; }

type state =
  { loc : loc;
    trace : loc list; }

(* type 'a world = *)
(*   { map : 'a map; *)
(*     transition : ('a map -> action -> 'a map); *)
(*     possible_actions : ('a map -> action list); } *)


(** Map *)

let in_grid map (x, y) =
  (0 <= x && x < map.x_lim) && (0 <= y && y < map.x_lim)

let is_blocked_loc map loc =
  map.feature loc = Wall

let is_allowed_state map loc =
  in_grid map loc && not (is_blocked_loc map loc)

let move map state action =
  let possible_next_loc =
    let (x, y) = state.loc in
    begin match action with
    | L -> (x - 1, y)
    | R -> (x + 1, y)
    | U -> (x, y + 1)
    | D -> (x, y - 1)
    end
  in
  if is_allowed_state map possible_next_loc then
    { loc = possible_next_loc;
      trace = possible_next_loc :: state.trace; }
  else
    state

let map_of_array grid =
  let array_rev a =
    let len = Array.length a in
    Array.mapi (fun i _ -> a.(len - 1 - i)) a
  in
  let grid = array_rev grid in
  { feature = (fun (x, y) -> grid.(y).(x));
    x_lim = Array.length grid.(0);
    y_lim = Array.length grid; }

let init_state loc_init =
  { loc = loc_init;
    trace = []; }

let pre_loc state =
  begin match state.trace with
  | loc :: _ -> Some loc
  | [] -> None
  end

let print string_of_value map state =
  let print_sep_line () =
    Format.printf "+";
    for i = 0 to map.x_lim - 1 do
      Format.printf "---+"
    done;
    Format.printf "@.";
  in
  print_sep_line();
  for j = map.y_lim - 1 downto 0 do
    Format.printf "|";
    for i = 0 to map.x_lim - 1 do
      let s =
        if (i, j) = state.loc then ":-)"
        else
          begin match map.feature (i, j) with
          | Wall -> " # "
          | Empty -> "   "
          | Value v ->
            let s = string_of_value v in
            begin match String.length s with
            | 0 -> "   "
            | 1 -> " "^s^" "
            | 2 -> " "^s
            | 3 -> s
            | _ -> (String.sub s 0 2)^"."
            end
          end
      in
      Format.printf "%s|" s;
    done;
    Format.printf "@.";
    print_sep_line()
  done


(** Transition *)

let make_world_deterministic options =
  let with_no_reverse = List.exists (fun x -> x = Opt_no_reverse) options in
  let transition map state action = move map state action in
  let possible_actions map state =
    List.filter
      (fun action ->
         let state' = move map state action in
         if with_no_reverse && Some state'.loc = pre_loc state then
           false
         else
           state'.loc <> state.loc)
      [ L; R; U; D; ]
  in
  (transition, possible_actions)


(** Actions *)

let string_of_action action =
  begin match action with
  | L -> "L"
  | R -> "R"
  | U -> "U"
  | D -> "D"
  end

let action_of_string s =
  begin match s with
  | "L" | "l" -> Some L
  | "R" | "r" -> Some R
  | "U" | "u" -> Some U
  | "D" | "d" -> Some D
  | _ -> None
  end


(** Graphics *)

let square_size map =
  let size_x = (Graphics.size_x() - map.x_lim - 1) / map.x_lim in
  let size_y = (Graphics.size_y() - map.y_lim - 1) / map.y_lim in
  let size = min size_x size_y in
  size - (size mod 2)

let square_center size (x, y) =
  let o_x = 1 + size / 2 + (size + 1) * x in
  let o_y = 1 + size / 2 + (size + 1) * y in
  (o_x, o_y)

let square_of_loc map (x, y) =
  let size = square_size map in
  let center = square_center size (x, y) in
  (center, size)

let draw_wall (center, size) =
  Graphics.set_color (Graphics.rgb 100 100 100);
  let c_x, c_y = center in
  let o_x, o_y =  (c_x - size / 2, c_y - size / 2) in
  Graphics.fill_rect o_x o_y (size - 1) (size - 1)


let draw_state ((c_x, c_y), size) =
  Graphics.set_color Graphics.blue;
  Graphics.fill_circle c_x c_y (max 1 (size / 3))

let draw_grid map =
  Graphics.set_color Graphics.black;
  let size = square_size map in
  let top = (size + 1) * map.y_lim in
  let right = (size + 1) * map.x_lim in
  for i = 0 to map.x_lim do
    let x = (size + 1) * i in
    Graphics.draw_segments [| x, 0, x, top |]
  done;
  for j = 0 to map.y_lim do
    let y = (size + 1) * j in
    Graphics.draw_segments [| 0, y, right, y |]
  done;
  ()

let draw map state =
  Graphics.clear_graph ();
  draw_grid map;
  for i = 0 to map.x_lim - 1 do
    for j = 0 to map.y_lim - 1 do
      begin match map.feature (i, j) with
      | Wall -> draw_wall (square_of_loc map (i, j))
      | Empty -> ()
      | Value v -> ()
      end;
      if (i, j) = state.loc then draw_state (square_of_loc map (i, j))
    done
  done;
  Graphics.synchronize();
  ()

(** Tests *)

(* let () = *)
(*   let grid = *)
(*     [| *)
(*       [| Wall; Wall;       Empty; Empty; Empty; Wall;      Wall; |]; *)
(*       [| Wall; Value 1;    Empty; Empty; Empty; Value 42;  Wall; |]; *)
(*       [| Wall; Empty;      Empty; Empty; Empty; Value 400; Wall; |]; *)
(*       [| Wall; Value 4012; Empty; Empty; Empty; Empty;     Wall; |]; *)
(*       [| Wall; Value 5;    Empty; Empty; Empty; Empty;     Wall; |]; *)
(*       [| Wall; Wall;       Empty; Empty; Empty; Wall;      Wall; |]; *)
(*     |] *)
(*   in *)
(*   let map = map_of_array grid in *)
(*   let _, possible_actions = make_world_deterministic [] in *)
(*   let state = init_state (1, 3) in *)
(*   print string_of_int map state; *)
(*   Format.printf "Prossible actions = [ "; *)
(*   List.iter *)
(*     (fun a -> Format.printf "%s " (string_of_action a)) *)
(*     (possible_actions map state); *)
(*   Format.printf "]@."; *)
(*   Graphics.open_graph " 400x400"; *)
(*   draw map state; *)
(*   let _ = read_line () in *)
(*   () *)

