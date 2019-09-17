(** Inference with streaming delayed sampling *)

type pstate = Infer_pf.pstate

(** Marginalized distribution *)
type 'a mdistr =
  | MGaussian : float * float -> float mdistr
  | MBeta : float * float -> float mdistr
  | MBernoulli : float -> bool mdistr

(** Family of marginal distributions (used as kind) *)
type kdistr =
  | KGaussian
  | KBeta
  | KBernoulli

(** Conditionned distribution *)
type ('m1, 'm2) cdistr =
  | AffineMeanGaussian: float * float * float -> (float, float) cdistr
  | CBernoulli : (float, bool) cdistr

(** Random variable of type ['b] and with parent of type ['a] *)
type ('parent, 'a) ds_node =
  { ds_node_id : int;
    mutable ds_node_children : 'a ds_child list;
    mutable ds_node_state : ('parent, 'a) ds_state; }

and ('parent, 'a) ds_state =
  | Initialized:
      ('z, 'parent) ds_node * ('parent, 'a) cdistr -> ('parent, 'a) ds_state
  | Marginalized:
      'a mdistr * (('z, 'parent) ds_node * ('parent, 'a) cdistr) option -> ('parent, 'a) ds_state
  | Realized of 'a

and 'b ds_child =
    Child : ('b, 'c) ds_node -> 'b ds_child

(** {2 Distribution manipulations} *)

let mdistr_to_distr : type a.
  a mdistr -> a Distribution.t = fun mdistr ->
  begin match mdistr with
    | MGaussian (mu, var) -> Distribution.gaussian(mu, sqrt var)
    | MBeta (alpha, beta) -> Distribution.beta(alpha, beta)
    | MBernoulli p -> Distribution.bernoulli p
  end

let cdistr_to_mdistr : type a b.
  (a, b) cdistr -> a -> b mdistr =
  fun cdistr obs ->
    begin match cdistr with
      | AffineMeanGaussian (m, b, obsvar) ->
          MGaussian (m *. obs +. b, obsvar)
      | CBernoulli ->
          MBernoulli obs
    end

let make_marginal : type a b.
  a mdistr -> (a, b) cdistr -> b mdistr =
  fun mdistr cdistr ->
    begin match mdistr, cdistr with
      | MGaussian (mu, var), AffineMeanGaussian(m, b, obsvar) ->
          MGaussian (m *. mu +. b, m ** 2. *. var +. obsvar)
      | MBeta (a, b),  CBernoulli ->
          MBernoulli (a /. (a +. b))
      | _ -> assert false (* error "impossible" *)
    end

let make_conditional : type a b.
  a mdistr -> (a, b) cdistr -> b -> a mdistr =
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



(** {2 Graph manipulations} *)

let fresh_id =
  let cpt = ref (-1) in
  fun () ->
    incr cpt;
    !cpt

(* initialize without parent node *)
let assume_constant : type a parent.
  a mdistr -> (parent, a) ds_node =
  fun d ->
    { ds_node_id = fresh_id ();
      ds_node_children = [];
      ds_node_state = Marginalized (d, None); }

(* initialize with parent node *)
let assume_conditional : type a b c.
  (a, b) ds_node -> (b, c) cdistr -> (b, c) ds_node =
  fun par cdistr ->
    let child =
      { ds_node_id = fresh_id ();
        ds_node_children = [];
        ds_node_state = Initialized (par, cdistr); }
    in
    par.ds_node_children <- Child child :: par.ds_node_children;
    child

let marginalize : type a b.
  (a, b) ds_node -> unit =
  fun n ->
    (* Format.eprintf "marginalize: %s@." n.name; *)
    begin match n.ds_node_state with
      | Initialized (par, cdistr) ->
          let mdistr =
            begin match par.ds_node_state with
              | Realized x ->
                  cdistr_to_mdistr cdistr x
              | Marginalized (par_mdistr, _) ->
                  make_marginal par_mdistr cdistr
              | Initialized _ -> assert false (* error "marginalize'" *)
            end
          in
          n.ds_node_state <-
            Marginalized (mdistr, Some(par, cdistr))
      | _ ->
          Format.eprintf "Error: marginalize@.";
          assert false
    end

let rec delete : type a b.
  (a, b) ds_node -> a ds_child list -> a ds_child list =
  fun n l ->
    begin match l with
      | [] -> assert false
      | Child x :: l ->
          if n.ds_node_id = x.ds_node_id then l
          else Child x :: (delete n l)
    end

let realize : type a b.
  b -> (a, b) ds_node -> unit =
  fun obs n ->
    (* Format.eprintf "realize: %s@." n.name; *)
    (* ioAssert (isTerminal n) *)
    begin match n.ds_node_state with
      | Initialized _ -> assert false
      | Realized _ -> assert false
      | Marginalized (mdistr, None) -> ()
      | Marginalized (mdistr, Some (par, cdistr)) ->
          begin match par.ds_node_state with
            | Marginalized (par_mdistr, edge) ->
                let mdistr = make_conditional par_mdistr cdistr obs in
                par.ds_node_state <- Marginalized (mdistr, None);
                par.ds_node_children <- delete n par.ds_node_children
            | _ -> assert false
          end
    end;
    List.iter (fun (Child c) -> marginalize c) n.ds_node_children;
    n.ds_node_state <- Realized obs;
    n.ds_node_children <- []

let sample : type a b.
  (a, b) ds_node -> unit =
  fun n ->
    (* Format.eprintf "sample: %s@." n.name; *)
    (* ioAssert (isTerminal n) *)
    begin match n.ds_node_state with
      | Marginalized (m, _) ->
          let x = Distribution.draw (mdistr_to_distr m) in
          realize x n
      | _ -> assert false (* error "sample" *)
    end

let factor' = Infer_pf.factor'
let factor = Infer_pf.factor

let observe : type a b.
  pstate -> b -> (a, b) ds_node -> unit =
  fun prob x n ->
    (* io $ ioAssert (isTerminal n) *)
    begin match n.ds_node_state with
      | Marginalized (mdistr, _) ->
          factor' (prob, Distribution.score(mdistr_to_distr mdistr, x));
          realize x n
      | _ -> assert false (* error "observe'" *)
    end

(* Invariant 2: A node always has at most one marginal Child *)
let marginal_child : type a b.
  (a, b) ds_node -> b ds_child option =
  let is_marginalized state =
    begin match state with
      | Marginalized _ -> true
      | _ -> false
    end
  in
  fun n ->
    List.find_opt
      (fun (Child x) -> is_marginalized x.ds_node_state)
      n.ds_node_children

let rec prune : type a b.
  (a, b) ds_node -> unit =
  function n ->
    (* Format.eprintf "prune: %s@." n.name; *)
    (* assert (isMarginalized (state n)) $ do *)
    begin match marginal_child n with
      | Some (Child child) -> prune child
      | None -> ()
    end;
    sample n

let rec graft : type a b.
  (a, b) ds_node -> unit =
  function n ->
    (* Format.eprintf "graft %s@." n.name; *)
    begin match n.ds_node_state with
      | Marginalized _ ->
          begin match marginal_child n with
            | Some (Child child) -> prune child
            | None -> ()
          end
      | Initialized (par, cdistr) ->
          graft par;
          marginalize n
      | Realized _ -> assert false
    end

let rec value: type a b.
  (a, b) ds_node -> b =
  fun n ->
    begin match n.ds_node_state with
      | Realized x -> x
      | _ ->
          graft n;
          sample n;
          value n
    end

let rec get_mdistr : type a b.
  (a, b) ds_node -> b mdistr =
  function n ->
    (* Format.eprintf "graft %s@." n.name; *)
    begin match n.ds_node_state with
      | Marginalized (m, _) -> m
      | Initialized (par, cdistr) ->
          let par_mdistr = get_mdistr par in
          make_marginal par_mdistr cdistr
      | Realized _ -> assert false
    end

let get_distr : type a b.
  (a, b) ds_node -> b Distribution.t =
  fun n ->
    begin match n.ds_node_state with
      | Realized x -> Distribution.Dist_support [ (x, 1.) ]
      | _ ->
          begin match get_mdistr n with
            | MGaussian (mu, sigma) -> Distribution.gaussian(mu, sigma)
            | MBeta (a, b) -> Distribution.beta(a, b)
            | MBernoulli p -> Distribution.bernoulli p
          end
    end

let observe_conditional : type a b c.
  pstate -> (a, b) ds_node -> (b, c) cdistr -> c -> unit =
  fun prob par cdistr obs ->
    let n = assume_conditional par cdistr in
    graft n;
    observe prob obs n

let get_distr_kind : type a b.
  (a, b) ds_node -> kdistr =
  fun n  ->
    begin match n.ds_node_state with
      | Initialized (_, AffineMeanGaussian _) -> KGaussian
      | Initialized(_, CBernoulli) -> KBernoulli
      | Marginalized (MGaussian _, _) -> KGaussian
      | Marginalized (MBeta _, _) -> KBeta
      | Marginalized (MBernoulli _, _) -> KBernoulli
      | Realized _ -> assert false
    end