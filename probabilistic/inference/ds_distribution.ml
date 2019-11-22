open Owl

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
      Mat.mat * Mat.mat * Mat.mat -> (Mat.mat, Mat.mat) cdistr
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
  fun mdistr cdistr obs ->
    begin match mdistr, cdistr with
      | Dist_gaussian(mu, var), AffineMeanGaussian(m, b, obsvar) ->
          let (mu', var') =
            gaussian_conditioning mu var
              ((obs -. b) /. m) (obsvar /. m ** 2.)
          in
          Dist_gaussian (mu', var')
      | Dist_mv_gaussian(mu0, sigma0), AffineMeanGaussianMV(m, b, sigma) ->
          let obs' = Mat.sub obs b in
          let innov = Mat.sub obs' (Mat.dot m mu0) in
          let innov_sigma = Mat.add (Mat.dot m (Mat.dot sigma0 (Mat.transpose m))) sigma in
          let gain = Mat.dot sigma0 (Mat.dot (Mat.transpose m) (Linalg.D.inv innov_sigma)) in
          let mu' = Mat.add mu0 (Mat.dot gain innov) in
          let sigma' =
              let kh = Mat.dot gain m in
              Mat.dot (Mat.sub (Mat.eye (Mat.row_num kh)) kh) sigma0
          in
          Dist_mv_gaussian (mu', sigma')

      | Dist_beta (a, b),  CBernoulli ->
          if obs then Dist_beta (a +. 1., b)
          else Dist_beta (a, b +. 1.)
      | _, _ -> assert false
    end
