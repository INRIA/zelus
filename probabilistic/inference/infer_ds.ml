(** Inference with delayed sampling *)

type pstate = {
  mutable score : float;
}

let factor (prob, f) =
  prob.score <- prob.score +. f

type mgaussiant = float
type 'a mtype = 'a

type 'a mdistr =
  | MGaussian : float * float -> mgaussiant mdistr
  (* MBeta :: !Double -> !Double -> MDistr MBetaT *)
  | MBernoulli : float -> bool mdistr

type ('m1, 'm2) cdistr =
  | AffineMeanGaussian: float * float * float -> (mgaussiant, mgaussiant) cdistr
  (* CBernoulli :: CDistr MBetaT MBernoulliT *)

type 'a state =
  | Initialized
  | Marginalized of 'a mdistr
  | Realized of 'a mtype

type ('a, 'b) dsdistr =
  | UDistr :  'b mdistr -> ('a, 'b) dsdistr
  | CDistr : ('z, 'm1) node * ('m1, 'm2) cdistr -> ('m1, 'm2) dsdistr

and ('a, 'b) node =
  { name : string;
    mutable children : 'b node_from list;
    mutable state : 'b state;
    mutable distr : ('a, 'b) dsdistr;
  }

and 'b node_from =
  NodeFrom : ('b, 'c) node -> 'b node_from

and ('a, 'b) node' = ('a, 'b) node

let recip x = 1. /. x

let mgaussian mu var = MGaussian (mu, var)
let affine_mean_gaussian m b var = AffineMeanGaussian (m, b, var)

(* gaussianConditioning :: Double -> Double -> Double -> Double -> (Double, Double) *)
let gaussian_conditioning mu var obs obsvar =
  let ivar = recip var in
  let iobsvar = recip obsvar in
  let inf = ivar +. iobsvar in
  let var' = recip inf in
  let mu' = (ivar *. mu +. iobsvar *. obs) /. inf in
  (mu', var')

let gaussian_mean_gaussian: float -> (mgaussiant, mgaussiant) cdistr =
  fun x ->
  AffineMeanGaussian (1., 0., x)

(* initialize without parent node *)
(* constant' :: String -> MDistr a -> Node z a *)
let assume_constant n d =
  { name = n;
    children = [];
    state = Marginalized d;
    distr = UDistr d; }

(* initialize with parent node *)
(* newConditional' :: String -> IORef (Node a b) -> CDistr b c -> IO (IORef (Node b c)) *)
let assume_conditional str par cdistr =
  let child =
    { name = str
    ; children = []
    ; state = Initialized
    ; distr = CDistr (par, cdistr) }
  in
  par.children <- NodeFrom child :: par.children;
  child


let cdistr_to_distr (type m) (type m'): (m, m') cdistr -> m mtype -> m' mdistr =
  fun cdistr obs ->
  begin match cdistr with
    | AffineMeanGaussian (m, b, obsvar) ->
        MGaussian (m *. obs +. b, obsvar)
  end

let make_marginal (type a) (type b): a mdistr -> (a, b) cdistr -> b mdistr =
  fun mdistr cdistr ->
  begin match mdistr, cdistr with
    | MGaussian (mu, var), AffineMeanGaussian(m, b, obsvar) ->
        MGaussian (m *. mu +. b, m ** 2. *. var +. obsvar)
    | MBernoulli _, _ -> assert false (* error "impossible" *)
  end

let make_conditional (type a) (type b):
  a mdistr -> (a, b) cdistr -> b mtype  -> a mdistr =
  fun mdistr cdistr obs ->
  begin match mdistr, cdistr with
    | MGaussian(mu, var), AffineMeanGaussian(m, b, obsvar) ->
        let (mu', var') =
          gaussian_conditioning mu var ((obs -. b) /. m) (obsvar /. m ** 2.)
        in
        MGaussian(mu', var')
    | MBernoulli _, _ -> assert false (* error "impossible" *)
  end


let marginalize (type a) (type b): (a, b) node -> unit =
  fun n ->
  (* writeLog ("marginalize' " ++ name n) *)
  (* Format.printf "marginalize: %s@." n.name; *)
  begin match n.state, n.distr with
  | Initialized, CDistr (par, cdistr) ->
      let marg =
       begin match par.state with
         | Realized x ->
             cdistr_to_distr cdistr x
         | Marginalized parMarginal ->
             make_marginal parMarginal cdistr
         | Initialized -> assert false (* error "marginalize'" *)
       end
      in
      (* Format.printf "marginalize: %s is marginalized!!!!@." n.name; *)
      n.state <- Marginalized marg
  | state, _ ->
      Format.eprintf "Error: marginalize: %s@." n.name;
      assert false (* error $  "marginalize': " ++ name n *)
  end

let mdistr_to_distr (type a): a mdistr -> a Distribution.t = fun mdistr ->
  begin match mdistr with
    | MGaussian (mu, var) -> Distribution.gaussian mu (sqrt var)
    | MBernoulli p -> Distribution.bernoulli p
  end

let rec delete n l =
  begin match l with
    | [] -> assert false
    | NodeFrom x :: l ->
        if Obj.repr x == Obj.repr n then l
        else NodeFrom x :: (delete n l)
  end

(* realize :: MType b -> IORef (Node a b) -> IO () *)
let realize (type a) (type b): b mtype -> (a, b) node -> unit =
  fun val_ n ->
  (* Format.printf "realize: %s@." n.name; *)
  (* writeLog ("realize " ++ name n) *)
  (* ioAssert (isTerminal n) *)
  begin match n.distr with
    | UDistr _ -> ()
    | CDistr (p, cdistr) ->
        begin match p.state with
        | Marginalized marg ->
            p.state <- Marginalized (make_conditional marg cdistr val_);
            p.children <- delete n p.children
        | _ -> assert false
        end
  end;
  List.iter (fun (NodeFrom c) -> marginalize c) n.children;
  n.state <- Realized val_;
  n.children <- []

(* sample :: IORef (Node a b) -> IO () *)
let sample (type a) (type b) : (a, b) node -> unit =
  fun n ->
  (* Format.printf "sample: %s@." n.name; *)
  (* ioAssert (isTerminal n) *)
  (* writeLog ("sample " ++ name n) *)
  begin match n.state with
    | Marginalized m ->
        let x = Distribution.draw (mdistr_to_distr m) in
        realize x n
    | _ -> assert false (* error "sample" *)
  end


(* observe :: MType b -> IORef (Node a b) -> M () *)
let observe (prob, x, n) =
  (* io $ ioAssert (isTerminal n) *)
  (* io $ writeLog ("observe " ++ name n) *)
  begin match n.state with
  | Marginalized marg ->
      factor (prob, Distribution.score (mdistr_to_distr marg) x);
      realize x n
  | _ -> assert false (* error "observe'" *)
  end

let is_marginalized state =
  begin match state with
  | Marginalized _ -> true
  | _ -> false
  end

(* Invariant 2: A node always has at most one marginal Child *)
(* marginalChild :: Node a b -> IO (Maybe (RefNodeFrom b)) *)
let marginal_child n =
  List.find_opt
    (fun (NodeFrom x) -> is_marginalized x.state)
    n.children

(* (\* prune :: IORef (Node a b) -> IO () *\) *)
let rec prune : 'a 'b. ('a, 'b) node -> unit = function n ->
  (* Format.printf "prune: %s@." n.name; *)
  (* n <- readIORef nref *)
  (* writeLog ("prune " ++ name n) *)
  (* assert (isMarginalized (state n)) $ do *)
  begin match marginal_child n with
    | Some (NodeFrom child) ->
        prune child
    | None ->
        ()
  end;
  sample n


(* graft :: IORef (Node a b) -> IO () *)
let rec graft : 'a 'b. ('a, 'b) node -> unit = function n ->
  (* writeLog ("graft " ++ name n) *)
  (* Format.printf "graft %s@." n.name; *)
  begin match n.state with
  | Marginalized _ ->
      begin match marginal_child n with
        | Some (NodeFrom child) -> prune child
        | None -> ()
      end
  | _ ->
      begin match n.distr with
        | UDistr _ -> assert false (* error "graft" *)
        | CDistr (par, cdistr) ->
            graft par;
            marginalize n
      end
  end

(* obs :: MType b -> IORef (Node a b) -> M () *)
let obs (type a) (type b): pstate -> b mtype -> (a, b) node -> unit =
  fun prob x n ->
  graft n;
  observe (prob, x, n)


(* getValue :: IORef (Node a b) -> IO (MType b) *)
let rec get_value n =
  (* n <- readIORef nref *)
  begin match n.state with
  | Realized x -> x
  | _ ->
      graft n;
      sample n;
      get_value n
  end


let print_state n =   (* XXX TODO XXX *)
  Format.printf "%s:" n.name;
  begin match n.state with
  | Initialized -> Format.printf "Initialized"
  | Marginalized (MGaussian (mu, var)) ->
      Format.printf "Marginalized (MGaussian (%f, %f))" mu var
  | Realized x -> Format.printf "Realized %f" x
  end;
  Format.printf "@."

(* observeConditional :: Eq (MType b) => Eq (MType c) => String -> IORef (Node a b) -> CDistr b c -> MType c -> M () *)
let observe_conditional (type a) (type b) (type c): pstate -> string -> (a, b) node -> (b, c) cdistr -> c mtype -> unit =
  fun prob str n cdistr observation ->
  let y = assume_conditional str n cdistr in
  obs prob observation y



type 'a infer_state =
  { znode_state : 'a;
    pstate : pstate; }

open Ztypes

let infer (Node { alloc; reset; step }) =
  let alloc () =
    { znode_state = alloc ();
      pstate = { score = 0. }; }
  in
  let reset state =
    reset state.znode_state;
    state.pstate.score <- 0.
  in
  let step state input =
    step state.znode_state (state.pstate, input)
  in
  Node { alloc; reset; step }



(* (\* ----------------------------------------------------------------------- *\) *)
(* (\* Examples *\) *)
(* let delay_triplet zobs = *)
(*   let prob = { score = 0. } in *)
(*   let x = assume_constant "x" (MGaussian (0., 1.)) in *)
(*   Format.printf "x created@."; *)
(*   let y = assume_conditional "y"  x (gaussian_mean_gaussian 1.) in *)
(*   Format.printf "y created@."; *)
(*   let z = assume_conditional "z" y (gaussian_mean_gaussian 1.) in *)
(*   Format.printf "z created@."; *)
(*   obs prob zobs z; *)
(*   Format.printf "z observed@."; *)
(*   Format.printf "%f@." (get_value z); *)
(*   Format.printf "%f@." (get_value x); *)
(*   Format.printf "%f@." (get_value y) *)

(* let () = *)
(*   Random.self_init (); *)
(*   delay_triplet 42. *)

