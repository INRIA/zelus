(** Inference with delayed sampling *)

type pstate = {
  mutable score : float;
}

type mgaussiant = float
type mbetat = float
type mbernoullit = bool
type 'a mtype = 'a

(** Marginalized distribution *)
type 'a mdistr =
  | MGaussian : float * float -> mgaussiant mdistr
  | MBeta : float * float -> mbetat mdistr
  | MBernoulli : float -> bool mdistr

(** Conditionned distribution *)
type ('m1, 'm2) cdistr =
  | AffineMeanGaussian: float * float * float -> (mgaussiant, mgaussiant) cdistr
  | CBernoulli : (mbetat, mbernoullit) cdistr

(** Node state *)
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


let factor (prob, f) =
  prob.score <- prob.score +. f

let mdistr_to_distr (type a): a mdistr -> a Distribution.t = fun mdistr ->
  begin match mdistr with
    | MGaussian (mu, var) -> Distribution.gaussian mu (sqrt var)
    | MBeta (alpha, beta) -> Distribution.beta alpha beta
    | MBernoulli p -> Distribution.bernoulli p
  end

let cdistr_to_mdistr (type m) (type m'): (m, m') cdistr -> m mtype -> m' mdistr =
  fun cdistr obs ->
  begin match cdistr with
    | AffineMeanGaussian (m, b, obsvar) ->
        MGaussian (m *. obs +. b, obsvar)
    | CBernoulli ->
        MBernoulli obs
  end


let mgaussian mu var = MGaussian (mu, var)
let mbeta alpha beta = MBeta (alpha, beta)
let mbernoulli theta = MBernoulli theta

let affine_mean_gaussian m b var = AffineMeanGaussian (m, b, var)

let gaussian_mean_gaussian: float -> (mgaussiant, mgaussiant) cdistr =
  fun x ->
  AffineMeanGaussian (1., 0., x)

let make_marginal (type a) (type b): a mdistr -> (a, b) cdistr -> b mdistr =
  fun mdistr cdistr ->
  begin match mdistr, cdistr with
    | MGaussian (mu, var), AffineMeanGaussian(m, b, obsvar) ->
        MGaussian (m *. mu +. b, m ** 2. *. var +. obsvar)
    | MBeta (a, b),  CBernoulli ->
        MBernoulli (a /. (a +. b))
    | _ -> assert false (* error "impossible" *)
  end

let make_conditional (type a) (type b):
  a mdistr -> (a, b) cdistr -> b mtype -> a mdistr =
  let gaussian_conditioning mu var obs obsvar =
    let ivar = 1. /. var in
    let iobsvar = 1. /. obsvar in
    let inf = ivar +. iobsvar in
    let var' = 1. /. inf in
    let mu' = (ivar *. mu +. iobsvar *. obs) /. inf in
    (mu', var')
  in
  fun mdistr cdistr obs ->
  begin match mdistr, cdistr with
    | MGaussian(mu, var), AffineMeanGaussian(m, b, obsvar) ->
        let (mu', var') =
          gaussian_conditioning mu var ((obs -. b) /. m) (obsvar /. m ** 2.)
        in
        MGaussian(mu', var')
    | MBeta (a, b),  CBernoulli ->
        if obs then MBeta (a +. 1., b) else MBeta (a, b +. 1.)
    | _, _ -> assert false (* error "impossible" *)
  end


(* initialize without parent node *)
let assume_constant (type a) (type z): string -> a mdistr -> (z, a) node =
  fun n d ->
  { name = n;
    children = [];
    state = Marginalized d;
    distr = UDistr d; }

(* initialize with parent node *)
(* newConditional' :: String -> IORef (Node a b) -> CDistr b c -> IO (IORef (Node b c)) *)
let assume_conditional (type a) (type b) (type c):
  string -> (a,b) node -> (b, c) cdistr -> (b, c) node =
  fun str par cdistr ->
  let child =
    { name = str
    ; children = []
    ; state = Initialized
    ; distr = CDistr (par, cdistr) }
  in
  par.children <- NodeFrom child :: par.children;
  child


let marginalize (type a) (type b): (a, b) node -> unit =
  fun n ->
  (* Format.printf "marginalize: %s@." n.name; *)
  begin match n.state, n.distr with
    | Initialized, CDistr (par, cdistr) ->
        let marg =
          begin match par.state with
            | Realized x ->
                cdistr_to_mdistr cdistr x
            | Marginalized parMarginal ->
                make_marginal parMarginal cdistr
            | Initialized -> assert false (* error "marginalize'" *)
          end
        in
        n.state <- Marginalized marg
    | state, _ ->
        Format.eprintf "Error: marginalize %s@." n.name;
        assert false
  end

let rec delete n l =
  begin match l with
    | [] -> assert false
    | NodeFrom x :: l ->
        if Obj.repr x == Obj.repr n then l
        else NodeFrom x :: (delete n l)
  end

let realize (type a) (type b): b mtype -> (a, b) node -> unit =
  fun val_ n ->
  (* Format.printf "realize: %s@." n.name; *)
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

let sample (type a) (type b) : (a, b) node -> unit =
  fun n ->
  (* Format.printf "sample: %s@." n.name; *)
  (* ioAssert (isTerminal n) *)
  begin match n.state with
    | Marginalized m ->
        let x = Distribution.draw (mdistr_to_distr m) in
        realize x n
    | _ -> assert false (* error "sample" *)
  end

let observe (type a) (type b): pstate -> b mtype -> (a, b) node -> unit =
  fun prob x n ->
  (* io $ ioAssert (isTerminal n) *)
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
let marginal_child (type a) (type b): (a, b) node -> b node_from option =
  fun n ->
  List.find_opt
    (fun (NodeFrom x) -> is_marginalized x.state)
    n.children

let rec prune : 'a 'b. ('a, 'b) node -> unit = function n ->
  (* Format.printf "prune: %s@." n.name; *)
  (* assert (isMarginalized (state n)) $ do *)
  begin match marginal_child n with
    | Some (NodeFrom child) ->
        prune child
    | None ->
        ()
  end;
  sample n

let rec graft : 'a 'b. ('a, 'b) node -> unit = function n ->
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

let obs (type a) (type b): pstate -> b mtype -> (a, b) node -> unit =
  fun prob x n ->
  graft n;
  observe prob x n

let rec get_value: 'a 'b. ('a, 'b) node -> 'b mtype =
  fun n ->
  begin match n.state with
    | Realized x -> x
    | _ ->
        graft n;
        sample n;
        get_value n
  end

let print_state n =   (* XXX TODO XXX *)
  Format.printf "%s: " n.name;
  begin match n.state with
  | Initialized -> Format.printf "Initialized"
  | Marginalized (MGaussian (mu, var)) ->
      Format.printf "Marginalized (MGaussian (%f, %f))" mu var
  | Marginalized _ -> Format.printf "Marginalized"
  | Realized x -> Format.printf "Realized %f" x
  end;
  Format.printf "@."

let observe_conditional (type a) (type b) (type c):
  pstate -> string -> (a, b) node -> (b, c) cdistr -> c mtype -> unit =
  fun prob str n cdistr observation ->
  let y = assume_conditional str n cdistr in
  obs prob observation y


open Ztypes

type 'a infer_state =
  { znode_state : 'a;
    pstate : pstate; }

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

