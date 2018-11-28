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

open Ztypes
    
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
          let Node { alloc; reset; step } = Infer.infer n node in
          let v = Pair { state = alloc (); trans = step } in
          s := Some(v); v
      | Some(v) -> v in
    trans state (c, input) in

  Node { alloc = alloc; reset = reset; step = step }
