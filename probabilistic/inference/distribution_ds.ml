type ('a, 'b) dist =
    | CDist : ('a, 'b) Infer_ds_ll.cdistr -> ('a, 'b) dist
    | UDist : 'b Infer_ds_ll.mdistr -> ('a, 'b) dist
;;

let gaussian variance = CDist (Infer_ds_ll.gaussian_mean_gaussian variance);;
let beta a b = UDist (MBeta (a, b));;
let bernoulli = CDist (CBernoulli);;
