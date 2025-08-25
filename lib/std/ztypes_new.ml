(* Actuellement *)
type ('a, 'b) node =
  Node : { alloc: unit -> 's;
           step : 's -> 'a -> 'b;
           copy : 's -> 's -> unit;
           reset : 's -> unit } -> ('a, 'b) node

type cvec = float Array.t
type zinvec = bool Array.t
type zoutvec = float Array.t

type cstate =
  { cvec: float Array.t;
    dvec: float Array.t;
    zin: bool Array.t;
    zout: float Array.t;
    cmax: int;
    zmax: int;
    mutable cindex: int;
    mutable zindex: int }

type ('a, 'b) hnode = cstate -> ('a, 'b) node

(* Pourrait-on plutot avoir un type ? *)
type ('p, 'r, 'a, 'b) node =
  Node : { alloc : 'p -> 's;
           step : 's -> 'a -> 'b;
           copy : 's -> 's -> unit;
           reset : 's -> 'r -> unit } -> ('p, 'r, 'a, 'b) node

(* Est-ce equivalent ? La creation (avec alloc) est parametree *)
(* Au lieu de:
 *- let Node { alloc = a1; step = s1; copy = c1; reset = r1 } = e cstate in
 *- ...
 *- on a:
 *- let Node { alloc = a1; step = s1; copy = c1; reset = r1 } = e in
 *- ...
 *- dans le code alloc, on a:
 *- let alloc cstate =
 *- ...
 *-   let s1 = a1 cstate in
 *-   let s2 = a2 cstate in
 *-   ...
 *- Ainsi, pour le code actuel de inout.ml, cela revient a ajouter un
 *- champ cstate dans l'etat de chacun.
 *- puis, pour le code a executer en plus (cf. inout.ml), on modifie
 *- [step self x] en [step s x = ... s.cpos.(i) <- ...] etc.
 *- on evite d'avoir [cstate] implicite qui est dans l'env. de fermeture.
 *- ca doit revenir au meme en terme d'efficacite (acces aux donnees).
 *- l'avantage, c'est que l'etape inout.ml manipule des valeurs qui
 *- sont toutes de type (_, 'a, 'b) node. La premiere est:
 *- (unit, 'a, 'b) node, la seconde est (cstate, 'a, 'b) node pour les
 *- noeuds hybrides. *)

type time = float

type 'a signal = Abs | Present of 'a

type 'a superdense =
  { horizon: time;
    u: (time -> 'a) signal }

type 'a dense =
  { horizon: time;
    u: time -> 'a }

type 'a superdense = 'a dense signal

type ('p, 'r, 'a, 'b, 'x, 'xder, 'zin, 'zout) hnode =
  Hnode : { alloc : 'p -> 's;
            step : 's -> 'a -> 'b;
            copy : 's -> 's -> unit;
            reset : 's -> 's -> unit;
            fder : 's -> 'a -> 'x -> 'xder;
            fzero : 's -> 'a -> 'x -> 'zout;
            fout : 's -> 'a -> 'x -> 'b;
            cset : 's -> 'x -> unit;
            cget : 's -> 'x;
            zset : 's -> 'zin -> unit;
            horizon : 's -> time;
          } ->
          ('p, 'r, 'a, 'b, 'x, 'xder, 'zin, 'zout) hnode

(* val lift : (cstate, 'a, 'b) node ->
                    (unit, 'a, 'b, cvec, cvec, zinvec, zoutvec) hnode *)
(* val solve :
   (cstate, 'a, 'b) node -> (unit, 'a superdense, 'b superdense) node *)

(* val check :
   (cstate, 'a, bool) node -> (unit, 'a dense, bool) node *)

(* Cas des noeuds avec assertions *)
type ('p, 'r, 'a, 'b) node =
  Node : { alloc : 'p -> 's;
           step : 's -> 'a -> 'b;
           copy : 's -> 's -> unit;
           reset : 's -> 'r -> unit;
           assertion : ('p, 'r, 's dense, bool) node option }
         -> ('p, 'r, 'a, 'b) node

(* Exemples:
 *- un noeud a temps discret, sans assertion:
 *-
 *- Node { alloc; step; copy; reset; assertion = None }
 *-
 *- un noeud a temps continu, avec assertion:
 *-
 *- let Node { alloc = alloc1; step = s1; assertion = a1 } = ... in
 *- ...
 *- let a2 = lift (Node { alloc = ...;... }) in
 *- let assertion = compose a1 a2 in
 *- ... *)

(* projections *)
let proj1 { horizon; u } = { horizon; u = fun t -> let v1, _ = u t in v1 }
let proj2 { horizon; u } = { horizon; u = fun t -> let _, v2 = u t in v2 }

(* Composer deux assertions *)
let rec compose :
          's1 's2. ('p, 'r, 's1 dense, bool) node option ->
            ('p, 'r, 's2 dense, bool) node option ->
          ('p, 'r, ('s1 * 's2) dense, bool) node option =
  fun a1 a2 -> 
  match a1, a2 with
  | None, None -> None
  | Some(Node({ step } as a1)), None ->
     Some(Node { a1 with step = fun self sdense -> step self (proj1 sdense) })
  | None, Some(Node({ step } as a2)) ->
     Some(Node { a2 with step = fun self sdense -> step self (proj2 sdense) })
  | Some(Node { alloc = alloc1; step = s1; copy = c1; reset = r1; assertion = a1 }),
    Some(Node { alloc = alloc2; step = s2; copy = c2; reset = r2; assertion = a2 }) ->
     let alloc p = (alloc1 p, alloc2 p) in
     let step (self1, self2) sdense =
       (s1 self1 (proj1 sdense)) && (s2 self2 (proj2 sdense)) in
     let copy (self1, self2) (self11, self22) =
       c1 self1 self11; c2 self2 self22 in
     let reset (self1, self2) r = r1 self1 r; r2 self2 r in
     let assertion = compose a1 a2 in
     Some(Node { alloc; step; copy; reset; assertion })

(* Est-ce efficace ? Ne serait-ce pas mieux de considerer qu'un noeud a une liste *)
(* d'assertions et que la machine qui simule le modele et verifie les assertions *)
(* les parcours recursivement (tel que c'etait formule initialement avec *)
(* Francois Bidet) ? *)

(* Ainsi, le type des noeuds avec assertions serait: *)
(* La fonction [solve] qui convertit un noeud a temps continu en un noeud *)
(* a temps discret doit parcourir recursivement les assertions *)
type ('p, 'r, 'a, 'b) node =
  Node : { alloc : 'p -> 's;
           step : 's -> 'a -> 'b;
           copy : 's -> 's -> unit;
           reset : 's -> 'r -> unit;
           assertion : ('p, 'r, 's dense, bool) node list }
         -> ('p, 'r, 'a, 'b) node

(* Dans ce cas, la composition d'assertion n'est pas tellement plus simple car il *)
(* faut ajouter les projections *)

(*
 *- let Node { alloc = alloc_1; step = s_1; assertion = a_list_1 } = ... in
 *- ...
 *- let Node { alloc = alloc_n; step = s_n; assertion = a_list_n } = ... in
 *- let alloc p = (alloc_1 p,...,alloc_n p) in
 *- let step (self_1,...,self_n) = s_1 self_1 ...;...; s_n self_n ... in
 *- let a_list_1 = List.map (apply (fun { horizon; u } ->
 *-                                         { horizon;
 *-                                           u = fun t ->
 *-                                                let self_1,...,self_n = u(t) in
 *-                                                self_1 }) a_list_1 in
 *- ...
 *- let a_list_n = List.map (apply (fun ... -> ...)) a_list_n in
 *- Node { alloc; step; assertion = a_list_1 @ ... @ a_list_n }

 *- ou:
 *-
 *- let apply proj (Node { alloc; step; assertion }) =
 *-   Node { alloc; step = fun self i = step self (proj i); assertion } *)

(* If faut des fonctions de lifting (node vers hnode), *)
(* de conversion d'un noeud a temps continu vers un noeud a temps discret *)
(* et de verification des assertions *)

(* val lift : (cstate, unit, 'a, 'b) node ->
                    (unit, 'a, 'b, cvec, cvec, zinvec, zoutvec) hnode *)
(* val solve :
   (cstate, unit, 'a, 'b) node -> (unit, 'a superdense, 'b superdense) node *)

(* val check :
   (cstate, 'a, bool) node -> (unit, 'a dense, bool) node *)

(* Odealus *)

(* Une autre interface ? *)
type ('p, 'r, 'a, 'b) node =
  Node : { alloc : 'p -> 's;
           step : 's -> 'a -> 'b;
           copy : 's -> 's -> unit;
           reset : 's -> 'r -> unit;
           assertion : ('p, 'r, 'c, bool) node option } -> ('p, 'r, 'a, 'b) node

(* Dans ce cas, la fonction de composition des assertions serait-elle plus simple ? *)
(* Je ne vois pas comment construire une valeur de ce type, cad comment compiler. *)

(* N'est-ce pas plus simple avec la forme suivante ? *)
type ('a, 'b) cnode_with_assertions =
  Node : { alloc : cstate -> 's;
           step : 's -> 'a -> 'b;
           copy : 's -> 's -> unit;
           reset : 's -> -> unit;
           assertion : ('s, bool) cnode_with_assertions list }
         -> ('p, 'r, 'a, 'b) node

 (*
  *- Dans ce cas, c'est la fonction de simulation qui se charge de produire une
  *- machine discrete pour le modele et qui verifie recursivement que les
  *- assertions sont vraies.

  val solve: solver -S-> (cstate, unit, 'a, 'b) node -S->
                         (unit, unit, 'a superdense, 'b superdense) node
  
*)
