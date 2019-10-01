(** Marginalized distribution *)
type 'a mdistr = 'a Distribution.t

(** Family of marginal distributions (used as kind) *)
type kdistr =
  | KGaussian
  | KBeta
  | KBernoulli
  | KValue
  | KOthers

(** Conditionned distribution *)
type ('m1, 'm2) cdistr =
  | AffineMeanGaussian: float * float * float -> (float, float) cdistr
  | CBernoulli : (float, bool) cdistr


(** {2 Distribution manipulations} *)

let cdistr_to_mdistr : type a b.
  (a, b) cdistr -> a -> b mdistr =
  fun cdistr obs ->
    begin match cdistr with
      | AffineMeanGaussian (m, b, obsvar) ->
          Distribution.gaussian (m *. obs +. b, obsvar)
      | CBernoulli ->
          Distribution.bernoulli obs
    end

let make_marginal : type a b.
  a mdistr -> (a, b) cdistr -> b mdistr =
  fun mdistr cdistr ->
    begin match mdistr, cdistr with
      | Dist_gaussian (mu, var), AffineMeanGaussian(m, b, obsvar) ->
          Distribution.gaussian (m *. mu +. b,
                                 m ** 2. *. var +. obsvar)
      | Dist_beta (a, b),  CBernoulli ->
          Distribution.bernoulli (a /. (a +. b))
      | _ -> assert false
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
      | Dist_gaussian(mu, var), AffineMeanGaussian(m, b, obsvar) ->
          let (mu', var') =
            gaussian_conditioning mu var
              ((obs -. b) /. m) (obsvar /. m ** 2.)
          in
          Dist_gaussian (mu', var')
      | Dist_beta (a, b),  CBernoulli ->
          if obs then Dist_beta (a +. 1., b)
          else Dist_beta (a, b +. 1.)
      | _, _ -> assert false
    end
