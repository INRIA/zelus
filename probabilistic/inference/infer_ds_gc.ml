(** Inference with delayed sampling *)
open Ztypes

type pstate = Infer_ds_ll_gc.pstate

let factor = Infer_ds_ll_gc.factor

type 'a random_var = RV : ('b, 'a) Infer_ds_ll_gc.random_var -> 'a random_var

type _ expr_tree =
    | Econst : 'a -> 'a expr_tree
    | Ervar : 'a random_var -> 'a expr_tree
    | Eplus : float expr * float expr -> float expr_tree
    | Emult : float expr * float expr -> float expr_tree
    | Eapp : ('a -> 'b) expr * 'a expr -> 'b expr_tree
    | Epair : 'a expr * 'b expr -> ('a * 'b) expr_tree
and 'a expr = {
  mutable value : 'a expr_tree;
}

let const : 'a. 'a -> 'a expr =
    begin fun v ->
        { value = Econst v; }
    end

let plus : float expr * float expr -> float expr =
    begin fun (e1, e2) ->
      begin match e1.value, e2.value with
      | Econst x, Econst y -> { value = Econst (x +. y); }
      | _ -> { value = Eplus (e1, e2); }
      end
    end

let ( +~ ) x y = plus (x, y)

let mult : float expr * float expr -> float expr =
    begin fun (e1, e2) ->
      begin match e1.value, e2.value with
      | Econst x, Econst y -> { value = Econst (x *. y); }
      | Ervar x, Econst y -> { value = Emult(e2, e1); }
      | _ -> { value = Emult(e1, e2); }
      end
    end

let ( *~ ) x y = mult (x, y)

let app  : type t1 t2. (t1 -> t2) expr * t1 expr -> t2 expr =
    begin fun (e1, e2) ->
      begin match e1.value, e2.value with
      | Econst f, Econst x -> { value = Econst (f x); }
      | _ -> { value = Eapp(e1, e2); }
      end
    end

let ( @@~ ) f e = app (f, e)

let pair (e1, e2) =
  { value = Epair (e1, e2) }

let rec eval : type t. t expr -> t =
    begin fun e ->
      begin match e.value with
        | Econst v -> v
        | Ervar (RV x) ->
            let v = Infer_ds_ll_gc.value x in
            e.value <- Econst v;
            v
        | Eplus (e1, e2) ->
            let v = eval e1 +. eval e2 in
            e.value <- Econst v;
            v
        | Emult (e1, e2) ->
            let v = eval e1 *. eval e2 in
            e.value <- Econst v;
            v
        | Eapp (e1, e2) ->
            let v = (eval e1) (eval e2) in
            e.value <- Econst v;
            v
        | Epair (e1, e2) ->
            let v = (eval e1, eval e2) in
            e.value <- Econst v;
            v
      end
    end

let rec fval : type t. t expr -> t =
    begin fun e ->
      begin match e.value with
        | Econst v -> v
        | Ervar (RV x) -> Infer_ds_ll_gc.fvalue x
        | Eplus (e1, e2) -> fval e1 +. fval e2
        | Emult (e1, e2) -> fval e1 *. fval e2
        | Eapp (e1, e2) -> (fval e1) (fval e2)
        | Epair (e1, e2) -> (fval e1, fval e2)
      end
    end

let rec string_of_expr e =
    begin match e.value with
    | Econst v -> string_of_float v
    | Ervar (RV x) -> "Random"
    | Eplus (e1, e2) -> "(" ^ string_of_expr e1 ^ " + " ^ string_of_expr e2 ^ ")"
    | Emult (e1, e2) -> "(" ^ string_of_expr e1 ^ " * " ^ string_of_expr e2 ^ ")"
    | Eapp (e1, e2) -> "App"
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
    | Eapp (_, _) ->
      (print_string "Cannot compute the mean of an application.\n");
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

let of_distribution d =
  { isample = (fun prob -> const (Distribution.draw d));
    iobserve = (fun (prob, obs) -> factor (prob, Distribution.score(d, obs))); }

let ds_distr_with_fallback d is iobs =
  let dsd =
    let state = ref None in
    (fun () ->
       begin match !state with
       | None ->
           let dsd = of_distribution (d()) in
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
        | Eapp (e1, e2) -> None
        end
    end



(** Gaussian distribution (gaussianPD in Haskell) *)
let gaussian (mu, std) =
  let d () = Distribution.gaussian(eval mu, std) in
  let is prob =
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
let beta(a, b) =
  let d () = Distribution.beta(a, b) in
  let is prob = Some {value = Ervar (RV (Infer_ds_ll_gc.assume_constant "" (MBeta (a, b)))) } in
  let iobs (pstate, obs) = None in
  ds_distr_with_fallback d is iobs

(** Bernoulli distribution (bernoulliPD in Haskell) *)
let bernoulli p =
  let d () = Distribution.bernoulli (eval p) in
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


let infer n (Node { alloc; reset; step; }) =
  let step state (prob, x) = fval (step state (prob, x)) in
  Infer_pf.infer n (Node { alloc; reset; step; })

let infer_ess_resample n threshold (Node { alloc; reset; step; }) =
  let step state (prob, x) = fval (step state (prob, x)) in
  Infer_pf.infer_ess_resample n threshold (Node { alloc; reset; step; })
