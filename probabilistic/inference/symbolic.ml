type ('var, 'a) exp =
  | Var of 'var
  | Sum of ('var, 'a) exp list
  | Prod of ('var, 'a) exp list
  | Const of 'a
  | Unop of unop * ('var, 'a) exp
  | Unit (* XXX To remove XXX *)

and unop = Log

let var x = Var x
let sum l = Sum l
let prod l = Prod l
let const v = Const v
let unop op e = Unop (op, e)

type 'a exp_fam =
  { suff_stats : (unit, float) exp list;
    ef_describe : float list -> string;
    mle : float list -> float list; }

type env =
  (int * (float exp_fam * float list)) list

let empty_env = []

let normal_nat_params mu sigma2 =
  [ mu /. sigma2; -1. /. (2. *. sigma2); ]


let normal_ef =
  let conv l =
    begin match l with
      | [eta1; eta2] ->
          let sigma2 = - 1. /. (2. *. eta2) in
          (sigma2 *. eta1, sigma2)
      | _ -> assert false
    end
  in
  let suff_stats =
    let x = Var () in [x; Prod [x; x] ;]
  in
  let ef_describe eta =
    let (mu, sigma2) = conv eta in
    "Normal(" ^ (string_of_float mu) ^ ", " ^ (string_of_float sigma2) ^ ")"
  in
  let mle l =
    begin match l with
      | [ mu; ex2] ->
          let sigma2 = ex2 -. mu ** 2. in
          normal_nat_params mu sigma2
      | _ -> assert false
    end
  in
  { suff_stats; ef_describe; mle; }


let gaussian_ll mu sigma2 x =
  (* - x^2 / sigma2 *)
  (*     + 2 * x * mu / sigma2 *)
  (*     - mu^2 / sigma2 *)
  (*          - log (2 * pi) - log sigma2 *)
  assert false (* XXX TODO XXX *)


let get_var e =
  begin match e with
  | Var x -> Some x
  | _ -> None
  end

let get_dist env e =
  begin match get_var e with
  | Some x ->
      begin try
          let (ef, natural_params) = List.assoc x env in
          ef.ef_describe natural_params
        with Not_found ->
          assert false
      end
  | None -> "Not a sampled variable"
  end
