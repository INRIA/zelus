(* Programmation probabiliste. *)
(* Ce que j'ai compris de la discussion avec Louis (5/09/2018) *)
(*- une fonction sample, typiquement qui rend une valeur aleatoire suivant
 *- une disbribution de probalibite;
 *- une fonction factor qui pondere la distribution du resultat v; on
  ajoute la valeur de son argument a la log probabilite d'avoir v ?
 *- une fonction infer, qui construit la distribution de proba. du resultat. Une
  realisation simple consiste a lancer plusieurs instances f_i de
  la fonction f, chaque f_i calculant une valeur pour factor.
  si m = sum_{i <= n} factor_i; la probabilite que la sortie soit v est
  factor_i / m. *)

(* Pour reproduire cela en data-flow synchrone *)
(*- Louis a ecrit au tableau un exemple de programme pour estimer
 *- la pente d'une suite. Je l'ecris ci-dessous (de memoire car je
 *- l'ai efface par megarde).

let node f (fa, input) =
  let rec v = Random.int 10 fby v in
  let rec cpt = v + (0 fby cpt) in
  (* on diminue le facteur d'autant que la distance entre n et cpt est grande *)
  let r = factor fa (- (abs (input - cpt))) in
  r, cpt

Que doit faire infer k f n ?

1. On lance k instances r_i, v_i = f (0.0 fby r_ii) n en parallele;
2. chacun calcule sa propre valeur de r_i;
2. au bout d'un certain temps (quand ?), on regarde la valeur de r_i, pour
  chaque instance i et on construit une distribution de probabilite;
  Comment ? Chaque instance donne une valeur du facteur. On construit
  une table i: [0..n-1] -> factor.
3. on normalise, en calculant la somme m = sum_{i}(factor_i);
  on associe au resultat v_i la probabilite factor_i / m.
4. On tire au hasard une nouvelle instance de l'etat s_i a partir de
  cette distribution de probabilite;
4. On continue l'execution, en reinialisant r_i a 0.0
*)

let factor f f0 = f +. f0

(* Un noeud Zelus discret est implemente par une valeur du type suivant *)
(*
type ('a, 'b) node =
    Node: { alloc : unit -> 's; (* 's est l'etat interne *)
            reset: 's -> unit; (* initialise l'etat *)
            step: 's -> 'a -> 'b; (* *)
          } -> ('a, 'b) node
*)
open Ztypes
let infer n (Node { alloc; reset; step }) =
    (* The infer function takes an integer, a node and returns a node *)
  let alloc () =
    Array.init n (fun _ -> alloc ()),
    Array.make n 0.0 in

  let reset (states, scores) =
    Array.iter reset states;
    Array.fill scores 0 n 0.0 in

  let step (states, scores) (c, input) =
    let values =
      Array.mapi
        (fun i state ->
           let score, value = step state (scores.(i), input) in
           scores.(i) <- score;
           value)
        states
    in
    if c then Normalize.resample (states, scores, values);
    Normalize.normalize values
  in
  Node { alloc = alloc; reset = reset; step = step }

(* val infer :
     int -S-> (factor * 'a -D-> float * 'b)
         -S-> bool * 'a -D-> 'b Distribution.t *)
(* on ecrit [infer n f (c, x)] ou [n: int], [f : factor 'a -D-> 'b * factor], *)
(* [c: bool] et [x: 'a] *)

(* une fonction run qui prend un flot de fonctions (a etat), un flot *)
(* et l'applique. Ce type d'application etait possible en Lucid Synchrone *)
type 'a pair = Pair : { state : 's; trans: 's -> 'a } -> 'a pair


(* run : ('a -D-> 'b) * 'a -D-> 'b *)
(* run : ('a -D-> 'b) -> 'a -D-> 'b *)
let run =
  let alloc () = ref None in
  let reset s = s := None in
  let step s (Node { alloc; reset; step }, input) =
    let Pair { state; trans } =
      match !s with
      | None -> let si = alloc () in
                let v = Pair { state = si; trans = step } in
                s := Some(v); v
      | Some(v) -> v in
    trans state input in
  Node { alloc = alloc; reset = reset; step = step }

(* Une version un peu rock'n roll de infer, qui prend un flot d'entiers, un *)
(* flot de noeud, et rend un noeud. *)

(* val infer_dyn :
     int * (factor * 'a -D-> 'b * factor) * bool * 'a -D-> 'b
         -S-> (factor * 'a) -D-> 'b * factor *)
(* int -> int -> int = int -S-> int -S-> int
   int -A-> int -A-> int *)

(* the infer function is a node that takes a stream of integers, *)
(* a stream of nodes, a boolean stream and an input stream *)
(* val infer_dyn :
     int * (factor * 'a -D-> float * 'b) * bool * 'a -D-> 'b Distribution.t *)
let infer_dyn =
  let alloc () = ref None in

  let reset s = s := None in

  let step s (n, node, c, input) =
    let Pair { state; trans } =
      match !s with
      | None ->
          let Node { alloc; reset; step } = infer n node in
          let v = Pair { state = alloc (); trans = step } in
          s := Some(v); v
      | Some(v) -> v in
    trans state (c, input) in

  Node { alloc = alloc; reset = reset; step = step }

(* iterate a stateful node a bounded number of times *)
(* val iterate : int -S-> 'b -S-> ('a -D-> 'b) -D-> int * 'a -D-> 'b *)
(* iterate n default f m x iterates f (max n m) times *)
let iterate n default (Node { alloc; reset; step }) =
  let alloc = alloc in
  let reset = reset in
  let step s (m, input) =
    let m = max n m in
    let r = ref default in
    for i = 0 to m do
      r := step s input
    done;
    !r in
  Node { alloc = alloc; reset = reset; step = step }


(* [memoize f x] is functionally equivalent to [f x] but stores *)
(* all the pairs (state, input) and the associated result *)

let memoize_step step (s, table) x =
  try
    Hashtbl.find table (s, x)
  with
  | Not_found ->
    let sc = Normalize.copy s in
    let o = step s x in
    Hashtbl.add table (sc, x) o;
    o

let memoize (Node { alloc; reset; step }) =
  let alloc () =
    alloc (), Hashtbl.create 7 in
  let reset (s, table) =
    reset s; Hashtbl.clear table in
  Node { alloc = alloc; reset = reset; step = memoize_step step }


let get_opt o =
  begin match o with
  | None -> assert false
  | Some v -> v
  end


(* let infer_depth n k (Node { alloc; reset; step }) = *)
(*     (\* The infer_depth function takes an integer (number of particles), *)
(*        a lookhead, a node and returns a node *\) *)

(*   let alloc () = *)
(*     Array.init n (fun _ -> alloc ()), *)
(*     Array.make n 0.0 in *)

(*   let reset (states, scores) = *)
(*     Array.iter reset states; *)
(*     Array.fill scores 0 n 0.0 in *)

(*   let step (states, scores) (c, input) = *)
(*     (\* First step *\) *)
(*     let values = Array.make n None in *)
(*     for i = 0 to n - 1 do *)
(*       let score, value = step states.(i) (scores.(i), input) in *)
(*       scores.(i) <- score; *)
(*       values.(i) <- Some value *)
(*     done; *)
(*     let states_ext = *)
(*       Array.mapi *)
(*         (fun i state -> state, (Normalize.copy state, get_opt values.(i))) *)
(*         states *)
(*     in *)
(*     Normalize.resample (states_ext, scores); *)
(*     for d = 1 to k do *)
(*       for i = 0 to n - 1 do *)
(*         let score, value = step (fst states_ext.(i)) (scores.(i), input) in *)
(*         scores.(i) <- score; *)
(*       done; *)
(*       Normalize.resample (states_ext, scores) *)
(*     done; *)
(*     let values = ref [] in *)
(*     Array.iteri *)
(*       (fun i (_, (state, v)) -> *)
(*          states.(i) <- state; *)
(*          values := v :: !values) *)
(*       states_ext; *)
(*     Normalize.normalize !values *)
(*   in *)

(*   Node { alloc = alloc; reset = reset; step = step } *)


let expectation scores =
  let s = Array.fold_left (+.) 0. scores in
  s /. float (Array.length scores)


let plan_step n k model_step =
  let table = Hashtbl.create 7 in
  let rec expected_utility (state, score) (ttl, input) =
    if ttl < 1 then score
    else
      let states = Array.init n (fun _ -> Normalize.copy state) in
      let scores = Array.make n 0.0 in
      let score' =
        Array.iteri
          (fun i state ->
             let score, _ = model_step state (scores.(i), input) in
             let eu =
               memoize_step
                 expected_utility ((state, score), table) (ttl - 1, input)
             in
             scores.(i) <- eu)
          states;
        let scores' = Array.copy scores in
        Normalize.resample (states, scores, scores');
        expectation scores'
      in
      score +. score'
  in
  let step states scores input =
    let values =
      Array.mapi
        (fun i state ->
           let score, value = model_step state (scores.(i), input) in
           scores.(i) <- expected_utility (state, score) (k, input);
           value)
        states
    in
    let states_scores_values =
      Array.mapi (fun i state -> (state, scores.(i), values.(i))) states
    in
    Normalize.resample (states, scores, states_scores_values);
    states_scores_values
  in
  step


let plan n k (Node model : (float * 't1, float * 't2) Ztypes.node) =
  let alloc () = ref (model.alloc ()) in
  let reset state = model.reset !state in
  let step_XXXX = plan_step n k model.step in
  let step plan_state input =
    let states = Array.init n (fun _ -> Normalize.copy !plan_state) in
    let scores = Array.make n 0.0 in
    let states_scores_values = step_XXXX states scores input in
    let dist = Normalize.normalize states_scores_values in
    let state', _, value = Distribution.draw dist in
    plan_state := state';
    value
  in
  Node { alloc = alloc; reset = reset; step = step }


type 'state infd_state =
  { infd_states : 'state array;
    infd_scores : float array; }

let infer_depth n k (Node model) =
  let alloc () =
    { infd_states = Array.init n (fun _ -> model.alloc ());
      infd_scores = Array.make n 0.0; }
  in
  let reset state =
    Array.iter model.reset state.infd_states;
    Array.fill state.infd_scores 0 n 0.0
  in
  let step infd_state input =
    let states_scores_values =
      plan_step n k
        model.step infd_state.infd_states infd_state.infd_scores input
    in
    let values = Array.map (fun (_, _, v) -> v) states_scores_values in
    Normalize.normalize values
  in
  Node { alloc = alloc; reset = reset; step = step }


let () = Random.self_init ()
