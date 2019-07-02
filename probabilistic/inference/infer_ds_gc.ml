(** Inference with delayed sampling *)

type pstate = Infer_ds_ll_gc.pstate

let factor = Infer_ds_ll_gc.factor

let infer = Infer_ds_ll_gc.infer

type 'a random_var = RV : ('b, 'a) Infer_ds_ll_gc.random_var -> 'a random_var

type _ expr_tree =
    | Econst : 'a -> 'a expr_tree
    | Ervar : 'a random_var -> 'a expr_tree
    | Eplus : float expr * float expr -> float expr_tree
    | Emult : float expr * float expr -> float expr_tree
and 'a expr = {
    mutable value : 'a expr_tree;
}

let const : 'a. 'a -> 'a expr = 
    begin fun v ->
        {
            value = Econst v;
        }
    end

let plus : float expr -> float expr -> float expr =
    begin fun e1 e2 ->
        {
            value = Eplus (e1, e2);
        }
    end

let mult : float expr -> float expr -> float expr =
    begin fun e1 e2 ->
        {
            value = Emult(e1,e2);
        }
    end

type 'a distribution =
  | DS_gaussian of float expr * float

let rec eval_float : float expr -> float =
    begin fun e ->
        let ret = 
            begin match e.value with
            | Econst v -> v
            | Ervar (RV x) -> Infer_ds_ll_gc.get_value x
            | Eplus (e1, e2) -> eval_float e1 +. eval_float e2
            | Emult (e1, e2) -> eval_float e1 *. eval_float e2
            end
        in

        e.value <- Econst ret;
        ret
    end

let eval_bool : bool expr -> bool =
    begin fun e ->
        let ret =
            begin match e.value with
            | Econst v -> v
            | Ervar (RV x) -> Infer_ds_ll_gc.get_value x
            end
        in

        e.value <- Econst ret;
        ret
    end


let rec string_of_expr e = 
    begin match e.value with
    | Econst v -> string_of_float v
    | Ervar (RV x) -> "Random"
    | Eplus (e1, e2) -> "(" ^ string_of_expr e1 ^ " + " ^ string_of_expr e2 ^ ")"
    | Emult (e1, e2) -> "(" ^ string_of_expr e1 ^ " * " ^ string_of_expr e2 ^ ")"
    end
    

let rec mean_expr : float expr -> float =
  function e ->
    begin match e.value with
    | Econst v -> v
    | Ervar (RV x) -> Infer_ds_ll_gc.mean x
    | Eplus (e1, e2) -> mean_expr e1 +. mean_expr e2
    | Emult (e, {value = Econst m})
    | Emult ({value = Econst m}, e) ->
        m *. mean_expr e
    | Emult (_, _) ->
      (print_string "Cannot compute the mean of multiplication.\n");
      assert false
    end


(* High level delayed sampling distribution (pdistribution in Haskell) *)
type 'a ds_distribution =
  { isample : (pstate -> 'a expr);
    iobserve : (pstate * 'a -> unit); }

let sample (prob, ds_distr) =
  ds_distr.isample prob

let observe (prob, ds_distr, o) =
  ds_distr.iobserve(prob, o)

let ds_distr_of_distr d =
  { isample = (fun prob -> const (Distribution.draw d));
    iobserve = (fun (prob, obs) -> factor (prob, Distribution.score d obs)); }

let ds_distr_with_fallback d is iobs =
  let dsd =
    let state = ref None in
    (fun () ->
       begin match !state with
       | None ->
           let dsd = ds_distr_of_distr (d()) in
           state := Some dsd;
           dsd
       | Some dsd -> dsd
       end)
  in
  let is' prob =
    begin match is prob with
    | None -> (dsd()).isample prob
    | Some x -> x
    end
  in
  let iobs' (prob, obs) =
    begin match iobs (prob, obs) with
    | None -> (dsd()).iobserve (prob, obs)
    | Some () -> ()
    end
  in
  { isample = is'; iobserve = iobs'; }


let type_of_random_var (RV rv) =
  Infer_ds_ll_gc.type_of_dsdistr rv.distr

(* An affine_expr is either a constant or an affine transformation of a
 * random variable *)
type affine_expr =
    (* Interpretation (m, x, b) such that the output is m * x + b *)
    | AErvar of float * float random_var * float
    | AEconst of float

let rec affine_of_expr : float expr -> affine_expr option =
    begin fun expr ->
        begin match expr.value with
        | Econst v -> Some (AEconst v)
        | Ervar var -> Some (AErvar (1., var, 0.))
        | Eplus (e1, e2) ->
            begin match (affine_of_expr e1, affine_of_expr e2) with
            | (Some (AErvar (m, x, b)), Some (AEconst v))
            | (Some (AEconst v), Some (AErvar (m, x, b))) -> Some (AErvar (m, x, b +. v))
            | _ -> None
            end
        | Emult (e1, e2) ->
            begin match (affine_of_expr e1, affine_of_expr e2) with
            | (Some (AErvar (m, x, b)), Some (AEconst v))
            | (Some (AEconst v), Some (AErvar (m, x, b))) -> Some (AErvar (m *. v, x, b *. v))
            | _ -> None
            end
        end
    end



(** Gaussian distribution (gaussianPD in Haskell) *)
let gaussian mu std =
  let d () = Distribution.gaussian (eval_float mu) std in
  let is prob =
    (*
    let mu' = const_of_realized mu in
    begin match get_affine1 mu' with
      | None -> None
      | Some (b, mx) ->
          begin match mx with
            | None ->
               let rv = Infer_ds_ll_gc.assume_constant "" (MGaussian(b, std)) in
               Some (forgettable_var rv)
            | Some (RV par, m) ->
                let ty = type_of_random_var (RV par) in
                begin match ty with
                | MGaussianT ->
                    let nref = Infer_ds_ll_gc.assume_conditional "" par (AffineMeanGaussian(m, b, std)) in
                    Some (forgettable_var nref)
                | _ -> None
                end
          end
    end
    *)

    begin match affine_of_expr mu with
    | Some (AEconst v) ->
      let rv = Infer_ds_ll_gc.assume_constant "" (MGaussian(v, std)) in
      Some { value = (Ervar (RV rv)) }
    | Some (AErvar (m, RV x, b)) ->
      let ty = type_of_random_var (RV x) in
      begin match ty with
      | MGaussianT ->
        let rv = Infer_ds_ll_gc.assume_conditional "" x (AffineMeanGaussian(m, b, std)) in
        Some { value = (Ervar (RV rv)) }
      | _ -> None
      end
    | None -> None
    end
  in
  let iobs (prob, obs) =
    (*
    let mu' = const_of_realized mu in
    begin match get_affine1 mu' with
      | None ->
          None
      | Some (b, None) ->
          None
      | Some (b, Some (RV par, m)) ->
          let ty = type_of_random_var (RV par) in
          begin match ty with
          | MGaussianT ->
              Some (Infer_ds_ll_gc.observe_conditional prob "" par (AffineMeanGaussian(m, b, std)) obs)
          | _ ->
              None
          end
    end
    *)
    begin match affine_of_expr mu with
    | Some (AEconst v) ->
      None
    | Some (AErvar (m, RV x, b)) ->
      let ty = type_of_random_var (RV x) in
      begin match ty with
      | MGaussianT ->
        Some (Infer_ds_ll_gc.observe_conditional prob "" x (AffineMeanGaussian(m, b, std)) obs)
      | _ -> None
      end
    | None -> None
    end
  in
  ds_distr_with_fallback d is iobs


(** Beta distribution (betaPD in Haskell) *)
let beta a b =
  let d () = Distribution.beta a b in
  let is prob = Some {value = Ervar (RV (Infer_ds_ll_gc.assume_constant "" (MBeta (a, b)))) } in
  let iobs (pstate, obs) = None in
  ds_distr_with_fallback d is iobs

(** Bernoulli distribution (bernoulliPD in Haskell) *)
let bernoulli p =
  let d () = Distribution.bernoulli (eval_float p) in
  let with_beta_prior f =
    begin match p.value with
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
          { value = Ervar (RV (Infer_ds_ll_gc.assume_conditional "" par Infer_ds_ll_gc.CBernoulli)) })
  in
  let iobs (prob, obs) =
    with_beta_prior
      (fun (RV par) -> Infer_ds_ll_gc.observe_conditional prob "" par Infer_ds_ll_gc.CBernoulli obs)
  in
  ds_distr_with_fallback d is iobs


