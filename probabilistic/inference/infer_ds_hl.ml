module type DS_ll_S = sig
  type pstate = Infer_pf.pstate
  type ('p, 'a) ds_node

  val factor' : Infer_pf.pstate * float -> unit
  val factor : (Infer_pf.pstate * float, unit) Ztypes.cnode
  val value : ('a, 'b) ds_node -> 'b
  val get_distr_kind : ('a, 'b) ds_node -> Ds_distribution.kdistr
  val get_distr : ('a, 'b) ds_node -> 'b Distribution.t

  val observe_conditional :
    pstate -> ('a, 'b) ds_node -> ('b, 'c) Ds_distribution.cdistr -> 'c -> unit

  val assume_constant : 'a Ds_distribution.mdistr -> ('p, 'a) ds_node
  val assume_conditional :
    ('a, 'b) ds_node -> ('b, 'c) Ds_distribution.cdistr -> ('b, 'c) ds_node
end

module Make(DS_ll: DS_ll_S) = struct
  open Ztypes
  open Ds_distribution

  type pstate = DS_ll.pstate

  let factor' = DS_ll.factor'
  let factor = DS_ll.factor

  type 'a random_var = RV : ('b, 'a) DS_ll.ds_node -> 'a random_var

  type _ expr_tree =
    | Econst : 'a -> 'a expr_tree
    | Ervar : 'a random_var -> 'a expr_tree
    | Eplus : float expr * float expr -> float expr_tree
    | Emult : float expr * float expr -> float expr_tree
    | Eapp : ('a -> 'b) expr * 'a expr -> 'b expr_tree
    | Epair : 'a expr * 'b expr -> ('a * 'b) expr_tree
    | Earray : 'a expr array -> 'a array expr_tree
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
        | Ervar _, Econst _ -> { value = Emult(e2, e1); }
        | _ -> { value = Emult(e1, e2); }
      end
    end

  let ( *~ ) x y = mult (x, y)

  let app : type t1 t2. (t1 -> t2) expr * t1 expr -> t2 expr =
    begin fun (e1, e2) ->
      begin match e1.value, e2.value with
        | Econst f, Econst x -> { value = Econst (f x); }
        | _ -> { value = Eapp(e1, e2); }
      end
    end

  let ( @@~ ) f e = app (f, e)

  let pair (e1, e2) =
    { value = Epair (e1, e2) }

  let array a =
    { value = Earray a }

  let rec eval : type t. t expr -> t =
    begin fun e ->
      begin match e.value with
        | Econst v -> v
        | Ervar (RV x) ->
            let v = DS_ll.value x in
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
        | Earray a ->
            Array.map eval a
      end
    end

  (* let rec fval : type t. t expr -> t =
     begin fun e ->
      begin match e.value with
        | Econst v -> v
        | Ervar (RV x) -> DS_ll.fvalue x
        | Eplus (e1, e2) -> fval e1 +. fval e2
        | Emult (e1, e2) -> fval e1 *. fval e2
        | Eapp (e1, e2) -> (fval e1) (fval e2)
        | Epair (e1, e2) -> (fval e1, fval e2)
      end
     end *)

  let rec string_of_expr e =
    begin match e.value with
      | Econst v -> string_of_float v
      | Ervar (RV _) -> "Random"
      | Eplus (e1, e2) ->
          "(" ^ string_of_expr e1 ^ " + " ^ string_of_expr e2 ^ ")"
      | Emult (e1, e2) ->
          "(" ^ string_of_expr e1 ^ " * " ^ string_of_expr e2 ^ ")"
      | Eapp (_e1, _e2) -> "App"
    end

  (* High level delayed sampling distribution (pdistribution in Haskell) *)
  type 'a ds_distribution =
    { isample : (pstate -> 'a expr);
      iobserve : (pstate * 'a -> unit); }

  let sample =
    let alloc () = () in
    let reset _state = () in
    let copy _src _dst = () in
    let step _state (prob, ds_distr) =
      ds_distr.isample prob
    in
    Cnode { alloc; reset; copy; step; }

  let observe =
    let alloc () = () in
    let reset _state = () in
    let copy _src _dst = () in
    let step _state (prob, (ds_distr, o)) =
      ds_distr.iobserve(prob, o)
    in
    Cnode { alloc; reset; copy; step; }

  let of_distribution d =
    { isample = (fun _prob -> const (Distribution.draw d));
      iobserve = (fun (prob, obs) -> factor' (prob, Distribution.score(d, obs))); }

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
    DS_ll.get_distr_kind rv

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
        | Eapp (_, _) -> None
      end
    end

  (** Gaussian distribution (gaussianPD in Haskell) *)
  let gaussian (mu, std) =
    let d () = Distribution.gaussian(eval mu, std) in
    let is _prob =
      begin match affine_of_expr mu with
        | Some (AEconst v) ->
            let rv = DS_ll.assume_constant (Dist_gaussian(v, std)) in
            Some { value = (Ervar (RV rv)) }
        | Some (AErvar (m, RV x, b)) ->
            begin match DS_ll.get_distr_kind x with
              | KGaussian ->
                  let rv = DS_ll.assume_conditional x (AffineMeanGaussian(m, b, std)) in
                  Some { value = (Ervar (RV rv)) }
              | _ -> None
            end
        | None -> None
      end
    in
    let iobs (prob, obs) =
      begin match affine_of_expr mu with
        | Some (AEconst _) ->
            None
        | Some (AErvar (m, RV x, b)) ->
            begin match DS_ll.get_distr_kind x with
              | KGaussian ->
                  Some (DS_ll.observe_conditional prob x (AffineMeanGaussian(m, b, std)) obs)
              | _ -> None
            end
        | None -> None
      end
    in
    ds_distr_with_fallback d is iobs


  (** Beta distribution (betaPD in Haskell) *)
  let beta(a, b) =
    let d () = Distribution.beta(a, b) in
    let is _prob =
      Some { value = Ervar (RV (DS_ll.assume_constant (Dist_beta (a, b)))) }
    in
    let iobs (_pstate, _obs) = None in
    ds_distr_with_fallback d is iobs

  (** Bernoulli distribution (bernoulliPD in Haskell) *)
  let bernoulli p =
    let d () = Distribution.bernoulli (eval p) in
    let with_beta_prior f =
      begin match p.value with
        | Ervar (RV par) ->
            begin match DS_ll.get_distr_kind par with
              | KBeta -> Some (f (RV par))
              | _ -> None
            end
        | _ -> None
      end
    in
    let is _prob =
      with_beta_prior
        (fun (RV par) ->
           { value = Ervar (RV (DS_ll.assume_conditional par CBernoulli)) })
    in
    let iobs (prob, obs) =
      with_beta_prior
        (fun (RV par) -> DS_ll.observe_conditional prob par CBernoulli obs)
    in
    ds_distr_with_fallback d is iobs

  (** Inference *)

  let rec distribution_of_expr : type a. a expr -> a Distribution.t =
    fun expr ->
    begin match expr.value with
      | Econst c -> Dist_support [c, 1.]
      | Ervar (RV x) -> DS_ll.get_distr x
      | Eplus (e1, e2) ->
          Dist_plus (distribution_of_expr e1, distribution_of_expr e2)
      | Emult (e1, e2) ->
          Dist_mult (distribution_of_expr e1, distribution_of_expr e2)
      | Eapp (e1, e2) ->
          Dist_app (distribution_of_expr e1, distribution_of_expr e2)
      | Epair (e1, e2) ->
          Dist_pair (distribution_of_expr e1, distribution_of_expr e2)
      | Earray a ->
          Dist_array (Array.map distribution_of_expr a)
    end


  let infer n (Cnode { alloc; reset; copy = _; step; }) =
    let alloc () = ref (alloc ()) in
    let reset state = reset !state in
    let step state (prob, x) = distribution_of_expr (step !state (prob, x)) in
    let copy src dst = dst := Normalize.copy !src in
    let Cnode {alloc = infer_alloc; reset = infer_reset;
               copy = infer_copy; step = infer_step;} =
      Infer_pf.infer n (Cnode { alloc; reset; copy = copy; step; })
    in
    let infer_step state i =
      Distribution.to_mixture (infer_step state i)
    in
    Cnode {alloc = infer_alloc; reset = infer_reset;
           copy = infer_copy;  step = infer_step; }


  let infer_ess_resample n threshold (Cnode { alloc; reset; copy = _; step; }) =
    let alloc () = ref (alloc ()) in
    let reset state = reset !state in
    let step state (prob, x) = distribution_of_expr (step !state (prob, x)) in
    let copy src dst = dst := Normalize.copy !src in
    let Cnode {alloc = infer_alloc; reset = infer_reset;
               copy = infer_copy; step = infer_step;} =
      Infer_pf.infer_ess_resample n threshold
        (Cnode { alloc; reset; copy; step; })
    in
    let infer_step state i =
      Distribution.to_mixture (infer_step state i)
    in
    Cnode {alloc = infer_alloc; reset = infer_reset;
           copy = infer_copy; step = infer_step;}

  let infer_bounded n (Cnode { alloc; reset; copy = _; step; }) =
    let alloc () = ref (alloc ()) in
    let reset state = reset !state in
    let step state (prob, x) = eval (step !state (prob, x)) in
    let copy src dst = dst := Normalize.copy !src in
    Infer_pf.infer n (Cnode { alloc; reset; copy; step; })


end
