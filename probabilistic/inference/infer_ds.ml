(** Inference with delayed sampling *)

type pstate = Infer_ds_ll.pstate

let factor = Infer_ds_ll.factor

type 'a random_var =
 RV : ('b, 'a) Infer_ds_ll.rv -> 'a random_var

type _ expr =
  | Econst : 'a -> 'a expr
  | Ervar : 'a random_var -> 'a expr
  | Eplus : float expr * float expr -> float expr
  | Emult : float expr * float expr -> float expr

type 'a distribution =
  | DS_gaussian of float expr * float


let rec eval_expr (type t): t expr -> t =
  function e ->
    begin match e with
    | Econst v -> v
    | Ervar (RV x) -> Infer_ds_ll.get_value x
    | Eplus (e1, e2) -> eval_expr e1 +. eval_expr e2
    | Emult (e1, e2) -> eval_expr e1 *. eval_expr e2
    end

(* *)
type 'a pdistribution =
  { isample : (pstate -> 'a expr);
    iobserve : (pstate * 'a -> unit); }

let pdistr_of_distr d =
  { isample = (fun prob -> Econst (Distribution.draw d));
    iobserve = (fun (prob, obs) -> factor (prob, Distribution.score d obs)); }

let pdistr_with_fallback d is iobs =
  let pd = pdistr_of_distr d in
  let is' prob =
    begin match is prob with
    | None -> pd.isample prob
    | Some x -> x
    end
  in
  let iobs' (prob, obs) =
    begin match iobs (prob, obs) with
    | None -> pd.iobserve (prob, obs)
    | Some () -> ()
    end
  in
  { isample = is'; iobserve = iobs'; }


let union_assoc =
  let rec union_assoc_sorted f l1 l2 =
    begin match l1, l2 with
      | [], l | l, [] -> l
      | (k1, v1) :: l1', (k2, v2) :: l2' ->
          if k1 = k2 then
            (k1, f k1 v1 v2) :: union_assoc_sorted f l1' l2'
          else if k1 < k2 then
            (k1, v1) :: union_assoc_sorted f l1' l2
          else
            (k2, v2) :: union_assoc_sorted f l1 l2'
    end
  in
  fun f l1 l2 ->
    union_assoc_sorted f (List.sort compare l1) (List.sort compare l2)

(* getAffine :: Num a => Expr a -> Maybe (Map (Maybe (RefNodeToT a)) a) *)
let rec get_affine e =
    begin match e with
    | Econst x -> Some [None, x]
    | Ervar i -> Some [Some i, 1.]
    | Eplus (e1, e2) ->
        begin match get_affine e1, get_affine e2 with
        | Some a1, Some a2 ->
            Some (union_assoc (fun _ v1 v2 -> v1 +. v2) a1 a2)
        | _, _ -> None
        end
    | Emult (e1, e2) ->
        begin match get_affine e1, get_affine e2 with
        | Some a1, Some a2 ->
            let exception Stop in
            let mult (x1, v1) (x2, v2) =
              begin match x1, x2 with
              | None, None -> None, v1 *. v2
              | Some x, None | None, Some x -> Some x, v1 *. v2
              | Some _, Some _ -> raise Stop
              end
            in
            begin try
              Some
                (List.fold_left
                   (fun acc (x1, v1) ->
                      let l =
                        List.map (fun (x2, v2) -> mult (x1, v2) (x2, v2)) a2
                      in
                      union_assoc (fun _ v1 v2 -> v1 +. v2) acc l)
                   [] a1)
            with Stop -> None
            end
            (* Some (union_assoc (fun _ x y -> x +. y) a1 a2) *)
        | _, _ -> None
        end
    end

(* toAffine :: Num v => Map (Maybe k) v -> Maybe (v, Maybe (k, v)) *)
let to_affine p =
  begin match p with
  | None -> None
  | Some [] -> Some (0., None)
  | Some [ (None, v) ] -> Some (v, None)
  | Some [ (Some x, v) ] -> Some (0., Some (x, v))
  | Some [ (None, v); (Some x, vx) ]
  | Some [ (Some x, vx); (None, v) ] -> Some (v, Some (x, v))
  | _ -> None
  end

let get_affine1 e = to_affine (get_affine e)


(* realizedToConst :: Expr a -> IO (Expr a) *)
let const_of_realized =
  let var_map rvar =
    begin match rvar with
    | RV { state = Realized x } -> Some x
    | _ -> None
    end
  in
  let rec f expr =
    begin match expr with
      | Econst x -> Econst x
      | Ervar i ->
          begin match var_map i with
            | None -> Ervar i
            | Some k -> Econst k
          end
      | Eplus (x, y) -> Eplus (f x, f y)
      | Emult (x, y) -> Emult (f x, f y)
    end
  in
  f

(* forgettableVar :: IORef (Node a b) -> M (Expr (MType b)) *)
let forgettable_var rv =
  Ervar (RV rv)

let type_of_random_var (RV rv) =
  Infer_ds_ll.type_of_dsdistr rv.distr

(* gaussianPD :: Expr Double -> Double -> PDistrF Double *)
let gaussian_pd mu std =
  let d = Distribution.gaussian (eval_expr mu) std in
  let is prob =
    let mu' = const_of_realized mu in
    begin match get_affine1 mu' with
      | None -> None
      | Some (b, mx) ->
          begin match mx with
            | None ->
               let rv = Infer_ds_ll.assume_constant "" (MGaussian(b, std)) in
               Some (forgettable_var rv)
            | Some (RV par, m) ->
                let ty = type_of_random_var (RV par) in
                begin match ty with
                | MGaussianT ->
                    let nref = Infer_ds_ll.assume_conditional "" par (AffineMeanGaussian(m, b, std)) in
                    Some (forgettable_var nref)
                | _ -> None
                end
          end
    end
  in
  let iobs (prob, obs) =
    let mu' = const_of_realized mu in
    begin match get_affine1 mu' with
      | None -> None
      | Some (b, None) -> None
      | Some (b, Some (RV par, m)) ->
          let ty= type_of_random_var (RV par) in
          begin match ty with
          | MGaussianT -> Some (Infer_ds_ll.observe_conditional prob "" par (AffineMeanGaussian(m, b, std)) obs)
          | _ -> None
          end
    end
  in
  pdistr_with_fallback d is iobs


(* betaPD :: Double -> Double -> PDistrF Double *)
let beta_pd a b =
  let d = Distribution.beta a b in
  let is prob = Some (forgettable_var (Infer_ds_ll.assume_constant "" (MBeta (a, b)))) in
  let iobs (pstate, obs) = None in
  pdistr_with_fallback d is iobs

(* bernoulliPD :: Expr Double -> PDistrF Bool *)
let bernoulli_pd p =
  let d = Distribution.bernoulli (eval_expr p) in
  let with_beta_prior f =
    begin match p with
      | Ervar (RV par) ->
          let ty = type_of_random_var (RV par) in
          begin match ty with
            | MBetaT -> Some (f (RV par))
            | _ -> None
          end
      | _ -> None
    end
  in
  let is prob =
    with_beta_prior
      (fun (RV par) ->
         forgettable_var (Infer_ds_ll.assume_conditional "" par Infer_ds_ll.CBernoulli))
  in
  let iobs (prob, obs) =
    with_beta_prior
      (fun (RV par) -> Infer_ds_ll.observe_conditional prob "" par Infer_ds_ll.CBernoulli obs)
  in
  pdistr_with_fallback d is iobs
