type ('var, 'a) exp =
  | Var of 'var
  | Sum of ('var, 'a) exp list
  | Prod of ('var, 'a) exp list
  | Const of 'a
  | Pow of ('var, 'a) exp * int
  | Unop of unop * ('var, 'a) exp

and unop = Log

let var x = Var x
let sum l = Sum l
let prod l = Prod l
let const v = Const v
let unop op e = Unop (op, e)

let sum1 = function
  | [] -> Const 0.
  | [x] -> x
  | xs -> Sum xs

let prod1 = function
  | [] -> Const 1.
  | [x] -> x
  | xs -> Prod xs

let rec concatMap f = function
  | [] -> []
  | a::tl ->
    let fa = f a in
    let ftl = concatMap f tl in
    fa @ ftl

let rec get_sum = function
  | Sum xs -> concatMap get_sum xs
  | Const 0. -> []
  | x -> [x]

let rec get_sum1' mk xs = function
  | [] -> (mk, xs)
  | (e :: es) -> (match e with
    | Sum a -> get_sum1' mk xs (a @ es)
    | Const k' -> get_sum1' (match mk with
      | None -> Some k'
      | Some k -> Some (k +. k')) xs es
    | _ -> get_sum1' mk (e :: xs) es)

let rec get_sum1 e = get_sum1' None [] [e]

let rec get_prod1' mk xs = function
  | [] -> (mk, xs)
  | (e :: es) -> (match e with
    | Sum a -> get_prod1' mk xs (a @ es)
    | Const k' -> get_prod1' (match mk with
      | None -> Some k'
      | Some k -> Some (k +. k')) xs es
    | _ -> get_prod1' mk (e :: xs) es)

let rec get_prod1 e = get_prod1' None [] [e]

let fold_option f mx my = match (mx, my) with
  | (Some x, Some y) -> Some (f x y)
  | (Some x, None) -> Some x
  | (None, Some y) -> Some y
  | (None, None) -> None

let sum1' (mk, es) (mk', es') = sum1 ((match fold_option (fun x y -> x +. y) mk mk' with
  | Some 0. -> fun xs -> xs
  | Some k -> List.cons (Const k)
  | None -> fun xs -> xs
  ) (es @ es'))

let prod1' (mk, es) (mk', es') = let xs = es @ es' in
  match fold_option (+.) mk mk' with
    | Some 0. -> Const 0.
    | Some 1. -> prod1 xs
    | Some k -> prod1 (Const k :: xs)
    | None -> prod1 xs

let rec get_prod = function
  | Prod xs -> concatMap get_prod xs
  | Const 1. -> []
  | x -> [x]

let get_sum_of_prod xs = List.map get_prod (get_sum xs)

let rec get_constants' combine mk xs = function
  | [] -> (mk, xs)
  | (e :: es) -> match e with
    | Const k' -> get_constants' combine (match mk with
      | None -> Some k'
      | Some k -> Some (combine k k')) xs es
    | _ -> get_constants' combine mk (e :: xs) es

let get_constants combine = get_constants' combine None []

let negate_prod es =
  let f = function
    | (None, xs) -> Const (-1.) :: xs
    | (Some k, xs) -> Const (-. k) :: xs
  in f (get_constants (fun x y -> x *. y) es)

let negate_exp e = prod1 (negate_prod (get_prod e))

let recip_exp = function
  | Const x -> Const (1. /. x)
  | Pow (e, k) -> Pow (e, -k)
  | e -> Pow (e, -1)

let option_map f = function
  | None -> None
  | Some x -> Some (f x)

let eplus x y = sum1' (get_sum1 x) (get_sum1 y)
let emul x y = prod1' (get_prod1 x) (get_prod1 y)
let enegate = negate_exp
let eminus x y = let (ky, ys) = get_sum1 y in
  sum1' (get_sum1 x) (option_map (fun x -> -. x) ky, List.map enegate ys)

let ediv x y = prod1 (get_prod x @ List.map recip_exp (get_prod y))

let eval_unop = function
  | Log -> log

let rec pow_int a = function
  | 0 -> 1.
  | 1 -> a
  | n ->
    let b = pow_int a (n / 2) in
    if n mod 2 = 0
      then b *. b
      else b *. b *. a

let eval env = let rec f = function
  | Var i -> env i
  | Sum xs -> List.fold_left (+.) 0. (List.map f xs)
  | Prod xs -> List.fold_left (fun x y -> x *. y) 1. (List.map f xs)
  | Const k -> k
  | Pow (e, k) -> pow_int (f e) k
  | Unop (g, x) -> eval_unop g (f x)
  in f

let rec get_var = function
  | Var i -> Some i
  | Sum [x] -> get_var x
  | Sum xs -> None
  | Prod [x] -> get_var x
  | Prod xs -> None
  | Pow(x, 1) -> get_var x
  | Pow (x, k) -> None
  | Unop (f, x) -> None
  | Const k -> None

let rec map_option_list f = function
  | [] -> Some []
  | x :: xs -> match f x with
    | None -> None
    | Some y -> option_map (List.cons y) (map_option_list f xs)

let rec get_constant = function
  | Var i -> None
  | Const x -> Some x
  | Sum xs -> option_map (List.fold_left (+.) 0.)
               (map_option_list get_constant xs)
  | Prod xs -> option_map (List.fold_left (fun x y -> x *. y) 0.)
               (map_option_list get_constant xs)
  | Pow (x, k) -> option_map (fun x -> pow_int x k) (get_constant x)
  | Unop (f, x) -> option_map (eval_unop f) (get_constant x)

let rec any f = function
  | [] -> false
  | x :: xs -> if f x then true else any f xs

let rec all f = function
  | [] -> true
  | x :: xs -> if f x then all f xs else false

let rec var_in i = function
  | Var j -> i = j
  | Unop (f, e) -> var_in i e
  | Sum xs -> any (var_in i) xs
  | Prod xs -> any (var_in i) xs
  | Pow (e, k) -> var_in i e
  | Const k -> false

let rec not_in e e' = match e with
  | Const k -> true
  | _ -> if e = e' then false else match e' with
    | Var j -> true
    | Unop (f, e'') -> not_in e e''
    | Sum xs -> all (not_in e) xs
    | Prod xs -> all (not_in e) xs
    | Pow (e'', k) -> not_in e e''
    | Const k -> true

module IntSet = Set.Make(struct type t = int let compare = compare end)

let rec all_vars = function
  | Var i -> IntSet.singleton i
  | Prod xs
  | Sum xs -> List.fold_left IntSet.union IntSet.empty (List.map all_vars xs)
  | Const k -> IntSet.empty
  | Pow (e, k) -> all_vars e
  | Unop (f, e) -> all_vars e

let map_vars fenv = let rec f = function
  | Var i -> Var (fenv i)
  | Sum xs -> Sum (List.map f xs)
  | Prod xs -> Prod (List.map f xs)
  | Const k -> Const k
  | Pow (e, k) -> Pow (f e, k)
  | Unop (op, e) -> Unop (op, f e)
  in f

type 'a exp_fam =
  { suff_stats : (unit, float) exp list;
    ef_describe : float list -> string;
    mle : float list -> float list; }

type env =
  (id * (float exp_fam * float list)) list
and id = int

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

let pi = 4.0 *. atan 1.0;;

let gaussian_ll mu sigma2 x =
  sum1 [ediv (enegate (emul x x)) sigma2
       ; ediv (prod1 [Const 2.; x; mu]) sigma2
       ; ediv (enegate (emul mu mu)) sigma2
       ; enegate (Unop (Log, Const (2. *. pi)))
       ; enegate (Unop (Log, sigma2))
      ]


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

module IntMap = Map.Make(struct type t = int let compare = compare end)

let variable_representation =
  let combine (mx, map1) (my, map2) =
    (fold_option (fun x y -> x *. y) mx my
    , IntMap.union (fun k x y -> Some (emul x y)) map1 map2) in
  let f e = match IntSet.elements (all_vars e) with
    | [] -> Some (get_constant e, IntMap.empty)
    | [i] -> Some (None, IntMap.singleton i (map_vars (fun _ -> ()) e))
    | _ -> None
  in fun e -> option_map (List.fold_left combine (None, IntMap.empty))
                (map_option_list f e)

let from_variable_representation (mx, mp) =
  let xs = match mx with
    | None -> []
    | Some x -> [Const x]
  in xs @ List.map (fun (i, e) -> map_vars (fun () -> i) e) (IntMap.bindings mp)
