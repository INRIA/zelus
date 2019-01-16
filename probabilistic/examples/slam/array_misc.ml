type 'a t = 'a array

let get a i =
  a.(i)

let set a i v =
  let a' = Array.copy a in
  a'.(i) <- v;
  a'

let of_list = Array.of_list

let make = Array.make

open Distribution

let split n d =
  begin match d with
  | Dist_sampler (draw, score) -> assert false
  | Dist_support support ->
      Array.init n
        (fun i ->
           let p_true, p_false =
             List.fold_left
               (fun (p_true, p_false) (b, p) ->
                  if b.(i) then (p_true +. p, p_false)
                  else (p_true, p_false +. p))
               (0., 0.) support
           in
           Dist_support [ (true, p_true); (false, p_false) ])
  end

let print to_string a =
  Format.printf "[ @[";
  Array.iter
    (fun x -> Format.printf "%s;@ " (to_string x))
    a;
  Format.printf "@]]"

let print_map_dist a =
  print
    (fun d ->
       begin match d with
       | Dist_support [ (true, p_true); (false, p_false) ] ->
           "(true, "^(string_of_float p_true)^"), ( false, "^(string_of_float p_true)^")"
       | _ -> assert false
       end)
    a
