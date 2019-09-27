open Ds_distribution

(** Inference with streaming delayed sampling *)

type pstate = Infer_pf.pstate

(** Random variable of type ['b] and with parent of type ['a] *)
type ('p, 'a) ds_node =
  { ds_node_id : int;
    mutable ds_node_state : ('p, 'a) ds_state; }

and ('p, 'a) ds_state =
  | Initialized:
      ('z, 'p) ds_node * ('p, 'a) cdistr
    -> ('p, 'a) ds_state
  | Marginalized:
      'a mdistr * (('a, 'z) ds_node * ('a, 'z) cdistr) option
    -> ('p, 'a) ds_state
  | Realized of 'a


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
      ds_node_state = Marginalized (d, None); }

(* initialize with parent node *)
let assume_conditional : type a b c.
  (a, b) ds_node -> (b, c) cdistr -> (b, c) ds_node =
  fun p cdistr ->
    let child =
      { ds_node_id = fresh_id ();
        ds_node_state = Initialized (p, cdistr); }
    in
    child

let marginalize : type a b.
  (a, b) ds_node -> unit =
  fun n ->
    begin match n.ds_node_state with
      | Initialized (p, cdistr) ->
          begin match p.ds_node_state with
            | Realized x ->
                let mdistr = cdistr_to_mdistr cdistr x in
                n.ds_node_state <- Marginalized(mdistr, None)
            | Marginalized (p_mdistr, None) ->
                p.ds_node_state <- Marginalized (p_mdistr, Some(n, cdistr));
                let mdistr = make_marginal p_mdistr cdistr in
                n.ds_node_state <- Marginalized(mdistr, None)
            | Initialized _ | Marginalized (_, Some _) -> assert false
          end
      | Realized _ | Marginalized _ ->
          Format.eprintf "Error: marginalize@.";
          assert false
    end

let realize : type a b.
  b -> (a, b) ds_node -> unit =
  fun obs n ->
    assert begin match n.ds_node_state with
      | Marginalized (mdistr, None) -> true
      | Initialized _ | Realized _ | Marginalized (_, Some _) -> false
    end;
    n.ds_node_state <- Realized obs


let force_condition : type a b.
  (a, b) ds_node -> unit =
  fun n ->
    begin match n.ds_node_state with
      | Marginalized (mdistr, Some(child, cdistr)) ->
          begin match child.ds_node_state with
            | Realized x ->
                let mdistr = make_conditional mdistr cdistr x in
                n.ds_node_state <- Marginalized(mdistr, None)
            | Initialized _ | Marginalized _ -> ()
          end
      | Initialized _ | Realized _ | Marginalized (_, None) -> ()
    end

let sample : type a b.
  (a, b) ds_node -> unit =
  fun n ->
    force_condition n;
    begin match n.ds_node_state with
      | Marginalized (m, None) ->
          let x = Distribution.draw (mdistr_to_distr m) in
          realize x n
      | Realized x -> ()
      | Initialized _  | Marginalized (_, Some _) -> assert false
    end

let factor' = Infer_pf.factor'
let factor = Infer_pf.factor

let observe : type a b.
  pstate -> b -> (a, b) ds_node -> unit =
  fun prob x n ->
    force_condition n;
    begin match n.ds_node_state with
      | Marginalized (mdistr, None) ->
          factor' (prob, Distribution.score(mdistr_to_distr mdistr, x));
          realize x n
      | Initialized _ | Realized _ | Marginalized (_, Some _) -> assert false
    end

let rec prune : type a b.
  (a, b) ds_node -> unit =
  function n ->
    begin match n.ds_node_state with
      | Marginalized(_, Some(c, _)) -> prune c
      | Initialized _ | Realized _ | Marginalized (_, None) -> ()
    end;
    sample n

let rec graft : type a b.
  (a, b) ds_node -> unit =
  function n ->
    begin match n.ds_node_state with
      | Marginalized (_, None) | Realized _  -> ()
      | Marginalized (_, Some(c, _)) -> prune c
      | Initialized (p, cdistr) ->
          graft p;
          force_condition p;
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
    force_condition n;
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
      | Initialized _ | Marginalized _ ->
          begin match get_mdistr n with
            | MGaussian (mu, sigma) -> Distribution.gaussian(mu, sigma)
            | MBeta (a, b) -> Distribution.beta(a, b)
            | MBernoulli p -> Distribution.bernoulli p
          end
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
      | Marginalized (MGaussian _, _) -> KGaussian
      | Initialized(_, CBernoulli) -> KBernoulli
      | Marginalized (MBernoulli _, _) -> KBernoulli
      | Marginalized (MBeta _, _) -> KBeta
      | Realized _ -> KValue
    end


(** Test Copy *)

let rec copy_node : type a b.
  (int, Obj.t) Hashtbl.t -> (a, b) ds_node -> (a, b) ds_node =
  fun tbl n  ->
    begin match Hashtbl.find_opt tbl n.ds_node_id with
      | None ->
          let state =
            begin match n.ds_node_state with
              | Realized x -> Realized x
              | Marginalized (mdistr, None) -> Marginalized (mdistr, None)
              | Marginalized (mdistr, Some (c, cdistr)) ->
                  assert begin match c.ds_node_state with
                    | Initialized _ -> false
                    | Marginalized _ | Realized _ -> true
                  end;
                  let c_copy = copy_node tbl c in
                  Marginalized (mdistr, Some (c_copy, cdistr))
              | Initialized (p, cdistr) ->
                  assert begin match p.ds_node_state with
                    | Marginalized (_, Some (c, _)) ->
                        c.ds_node_id <> n.ds_node_id
                    | Initialized _ | Marginalized (_, None) | Realized _ ->
                        true
                  end;
                  let p_copy = copy_node tbl p in
                  Initialized (p_copy, cdistr)
            end
          in
          let n =
            { ds_node_id = n.ds_node_id;
              ds_node_state = state }
          in
          Hashtbl.add tbl n.ds_node_id (Obj.repr n);
          n
      | Some o -> (Obj.obj o: (a, b) ds_node)
    end