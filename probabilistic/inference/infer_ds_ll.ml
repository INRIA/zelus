open Maths
open Ds_distribution

(** Inference with delayed sampling *)

type pstate = Infer_pf.pstate


(** Random variable of type ['b] and with parent of type ['a] *)
type ('p, 'a) ds_node =
  { ds_node_id : int;
    mutable ds_node_children : 'a ds_child list;
    mutable ds_node_state : ('p, 'a) ds_state; }

and ('p, 'a) ds_state =
  | Initialized:
      ('z, 'p) ds_node * ('p, 'a) cdistr
    -> ('p, 'a) ds_state
  | Marginalized:
      'a mdistr * (('z, 'p) ds_node * ('p, 'a) cdistr) option
    -> ('p, 'a) ds_state
  | Realized of 'a

and 'b ds_child =
    Child : ('b, 'c) ds_node -> 'b ds_child


(** {2 Graph manipulations} *)

let fresh_id =
  let cpt = ref (-1) in
  fun () ->
    incr cpt;
    !cpt

(* initialize without parent node *)
let assume_constant : type a p.
  a mdistr -> (p, a) ds_node =
  fun d ->
    { ds_node_id = fresh_id ();
      ds_node_children = [];
      ds_node_state = Marginalized (d, None); }

(* initialize with parent node *)
let assume_conditional : type a b c.
  (a, b) ds_node -> (b, c) cdistr -> (b, c) ds_node =
  fun p cdistr ->
    let child =
      { ds_node_id = fresh_id ();
        ds_node_children = [];
        ds_node_state = Initialized (p, cdistr); }
    in
    p.ds_node_children <- Child child :: p.ds_node_children;
    child

let marginalize : type a b.
  (a, b) ds_node -> unit =
  fun n ->
    begin match n.ds_node_state with
      | Initialized (p, cdistr) ->
          begin match p.ds_node_state with
            | Realized x ->
                let mdistr = cdistr_to_mdistr cdistr x in
                n.ds_node_state <- Marginalized (mdistr, None)
            | Marginalized (p_mdistr, _) ->
                let mdistr = make_marginal p_mdistr cdistr in
                n.ds_node_state <- Marginalized (mdistr, Some(p, cdistr))
            | Initialized _ -> assert false
          end
      | Marginalized _ | Realized _ -> assert false
    end

let rec delete : type a b.
  (a, b) ds_node -> a ds_child list -> a ds_child list =
  fun n l ->
    begin match l with
      | Child x :: l ->
          if n.ds_node_id = x.ds_node_id then l
          else Child x :: (delete n l)
      | [] -> assert false
    end

let realize : type a b.
  b -> (a, b) ds_node -> unit =
  fun obs n ->
    begin match n.ds_node_state with
      | Marginalized (_mdistr, None) -> ()
      | Marginalized (_mdistr, Some (p, cdistr)) ->
          begin match p.ds_node_state with
            | Marginalized (p_mdistr, edge) ->
                let mdistr = make_conditional p_mdistr cdistr obs in
                p.ds_node_state <- Marginalized (mdistr, edge);
                p.ds_node_children <- delete n p.ds_node_children
            | Initialized _ | Realized _ -> assert false
          end
      | Initialized _ | Realized _ -> assert false
    end;
    n.ds_node_state <- Realized obs;
    List.iter (fun (Child c) -> marginalize c) n.ds_node_children;
    n.ds_node_children <- []

let sample : type a b.
  (a, b) ds_node -> unit =
  fun n ->
    begin match n.ds_node_state with
      | Marginalized (m, _) ->
          let x = Distribution.draw m in
          realize x n
      | Initialized _ | Realized _ -> assert false
    end

let factor' = Infer_pf.factor'
let factor = Infer_pf.factor

let observe : type a b.
  pstate -> b -> (a, b) ds_node -> unit =
  fun prob x n ->
    begin match n.ds_node_state with
      | Marginalized (mdistr, _) ->
          factor' (prob, Distribution.score(mdistr, x));
          realize x n
      | Initialized _ | Realized _ -> assert false
    end

(* Invariant 2: A node always has at most one marginal Child *)
let marginal_child : type a b.
  (a, b) ds_node -> b ds_child option =
  let is_marginalized state =
    begin match state with
      | Initialized _ | Realized _ -> false
      | Marginalized _ -> true
    end
  in
  fun n ->
    List.find_opt
      (fun (Child x) -> is_marginalized x.ds_node_state)
      n.ds_node_children

let rec prune : type a b.
  (a, b) ds_node -> unit =
  function n ->
    begin match marginal_child n with
      | Some (Child child) -> prune child
      | None -> ()
    end;
    sample n

let rec graft : type a b.
  (a, b) ds_node -> unit =
  function n ->
    begin match n.ds_node_state with
      | Realized _ -> assert false
      | Marginalized _ ->
          begin match marginal_child n with
            | Some (Child child) -> prune child
            | None -> ()
          end
      | Initialized (p, _cdistr) ->
          graft p;
          marginalize n
    end

let rec value: type a b.
  (a, b) ds_node -> b =
  fun n ->
    begin match n.ds_node_state with
      | Realized x -> x
      | Marginalized _ | Initialized _ ->
          graft n;
          sample n;
          value n
    end

let rec get_mdistr : type a b.
  (a, b) ds_node -> b mdistr =
  function n ->
    begin match n.ds_node_state with
      | Marginalized (m, _) -> m
      | Initialized (p, cdistr) ->
          let p_mdistr = get_mdistr p in
          make_marginal p_mdistr cdistr
      | Realized _ -> assert false
    end

let get_distr : type a b.
  (a, b) ds_node -> b Distribution.t =
  fun n ->
    begin match n.ds_node_state with
      | Realized x -> Distribution.Dist_support [ (x, 1.) ]
      | Initialized _ | Marginalized _ -> get_mdistr n
    end

let observe_conditional : type a b c.
  pstate -> (a, b) ds_node -> (b, c) cdistr -> c -> unit =
  fun prob p cdistr obs ->
    let n = assume_conditional p cdistr in
    graft n;
    observe prob obs n

let get_distr_kind : type a b.
  (a, b) ds_node -> kdistr =
  fun n  ->
    begin match n.ds_node_state with
      | Initialized (_, AffineMeanGaussian _) -> KGaussian
      | Marginalized (Dist_gaussian _, _) -> KGaussian
      | Initialized (_, AffineMeanGaussianMV (_, _, _)) -> KMVGaussian
      | Marginalized (Dist_mv_gaussian (_, _), _) -> KMVGaussian
      | Initialized (_, CBernoulli) -> KBernoulli
      | Marginalized (Dist_bernoulli _, _) -> KBernoulli
      | Marginalized (Dist_beta _, _) -> KBeta
      | Marginalized (( Dist_sampler _
                      | Dist_support _), _) -> KOthers
      | Marginalized (Dist_sampler_float _, _) -> KOthers
      | Marginalized (Dist_mixture _, _) -> KOthers
      | Marginalized (Dist_pair _, _) -> KOthers
      | Marginalized (Dist_list _, _) -> KOthers
      | Marginalized (Dist_array _, _) -> KOthers
      | Marginalized (Dist_uniform_int _, _) -> KOthers
      | Marginalized (Dist_uniform_float _, _) -> KOthers
      | Marginalized (Dist_exponential _, _) -> KOthers
      | Marginalized (Dist_poisson _, _) -> KOthers
      | Marginalized (Dist_plus _, _) -> KOthers
      | Marginalized (Dist_mult _, _) -> KOthers
      | Marginalized (Dist_app _, _) -> KOthers
      | Realized _ -> assert false
    end


let shape : type a. ((a, matrix) ds_node) -> int =
    fun r ->
    begin match r.ds_node_state with
      | Initialized (_, AffineMeanGaussianMV (_, b, _)) ->
	  let rows, _ = Mat.shape b in rows
      | Marginalized (Dist_mv_gaussian(mu, _), _) ->
	  let rows, _ = Mat.shape mu in rows
      | Realized v ->
	  let rows, _ = Mat.shape v in rows
      | Initialized (_, _) -> assert false
      | Marginalized (_, _) -> assert false
    end
