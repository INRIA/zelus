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
           reset : 'r -> 's -> unit } -> ('p, 'r, 'a, 'b) node

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
            reset : 'r -> 's -> unit;
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
           reset : 'r -> 's -> unit;
           assertion : ('p, 'r, 's dense, unit) node option }
         -> ('p, 'r, 'a, 'b) node

(* Exemples:
 *- un noeud a temps discret, sans assertion:
 *-
 *- Node { alloc; step; copy; reset; assertion = None }
 *-
 *- un noeud a temps continu, avec assertion:
 *-
 *- let Node { alloc = a1; step = s1; assertion = a1 } = ... in
 *- ...
 *- let a2 = lift (Node { alloc = ...;... }) in
 *- let assertion = compose a1 a2 in
 *- ... *)

(* Composer deux assertions *)
let compose a1 a2 =
  match a1, a2 with
  | None, None -> None
  | Some _, None -> a1
  | _, Some _ -> a2
  | Some(Node { alloc = alloc1; step = s1; copy = c1; reset = r1; assertion = a1 },
         Node { alloc = alloc2; step = s1; copy = c2; reset = r2; assertion = a2 }) ->
     let alloc p = (alloc1 p, alloc2 p) in
     let step
     
