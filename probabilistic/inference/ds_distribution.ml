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
      | MGaussian(mu, var), AffineMeanGaussian(m, b, obsvar) ->
          let (mu', var') =
            gaussian_conditioning mu var ((obs -. b) /. m) (obsvar /. m ** 2.)
          in
          MGaussian(mu', var')
      | MBeta (a, b),  CBernoulli ->
          if obs then MBeta (a +. 1., b) else MBeta (a, b +. 1.)
      | _, _ -> assert false
    end