open Maths

(** Marginalized distribution *)
type 'a mdistr = 'a Distribution.t

(** Family of marginal distributions (used as kind) *)
type kdistr =
  | KGaussian
  | KMVGaussian
  | KBeta
  | KBernoulli
  | KValue
  | KOthers

(** Conditionned distribution *)
type ('m1, 'm2) cdistr =
  | AffineMeanGaussian: float * float * float -> (float, float) cdistr
  | AffineMeanGaussianMV :
      matrix * matrix * matrix -> (matrix, matrix) cdistr
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
      | AffineMeanGaussianMV (m, b, sigma) ->
          Distribution.mv_gaussian (Mat.add (Mat.dot m obs) b, sigma)
    end

let make_marginal : type a b.
  a mdistr -> (a, b) cdistr -> b mdistr =
  fun mdistr cdistr ->
    begin match mdistr, cdistr with
      | Dist_gaussian (mu, var), AffineMeanGaussian(m, b, obsvar) ->
          Distribution.gaussian (m *. mu +. b,
                                 m ** 2. *. var +. obsvar)
      | Dist_mv_gaussian (mu0, sigma0), AffineMeanGaussianMV(m, b, sigma) ->
	  let mu' = Mat.add (Mat.dot m mu0) b in
          let sigma' =
            Mat.add (Mat.dot (Mat.dot m sigma0) (Mat.transpose m)) sigma
           in
           Distribution.mv_gaussian (mu', sigma')
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
  let mv_gaussian_conditioning mu0 sigma0 obs sigma =
    let sig0inv = Linalg.inv sigma0 in
    let siginv = Linalg.inv sigma in
    let sig0' = Linalg.inv (Owl.Mat.add sig0inv siginv) in
    let mu0' =
      Mat.dot sig0' (Mat.add (Mat.dot sig0inv mu0) (Mat.dot siginv obs))
    in
    (mu0', sig0')
  in
  fun mdistr cdistr obs ->
    begin match mdistr, cdistr with
      | Dist_gaussian(mu, var), AffineMeanGaussian(m, b, obsvar) ->
          let (mu', var') =
            gaussian_conditioning mu var
              ((obs -. b) /. m) (obsvar /. m ** 2.)
          in
          Dist_gaussian (mu', var')
      | Dist_mv_gaussian(mu0, sigma0), AffineMeanGaussianMV(m, b, sigma) ->
          let minv = Linalg.inv m in
          let (mu', var') =
            mv_gaussian_conditioning mu0 sigma0
              (Mat.dot minv (Mat.sub obs b))
              (Mat.dot minv (Mat.dot sigma (Mat.transpose minv))) in
          Dist_mv_gaussian (mu', var')

      | Dist_beta (a, b),  CBernoulli ->
          if obs then Dist_beta (a +. 1., b)
          else Dist_beta (a, b +. 1.)
      | _, _ -> assert false
    end
