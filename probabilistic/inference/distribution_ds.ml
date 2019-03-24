type ('a, 'b) dist =
    | CDist : ('a, 'b) Infer_ds.cdistr -> ('a, 'b) dist
    | UDist : 'b Infer_ds.mdistr -> ('a, 'b) dist
;;

let gaussian variance = CDist (Infer_ds.gaussian_mean_gaussian variance);;
let beta a b = UDist (MBeta (a, b));;
let bernoulli = CDist (CBernoulli);;
