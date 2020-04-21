(* Set of values *)
type bvalue =
  | Vint : int -> bvalue
  | Vbool : bool -> bvalue
  | Vfloat : float -> bvalue
  | Vvoid : bvalue

type value =
  | Value : bvalue -> value
  | Vtuple : value list -> value
  | Vconstr0 : Lident.t -> value
  | Vbot : value
  | Vnil : value
 
type state =
  | Sempty : state
  | Stuple : state list -> state
  | Sval : value -> state
  | Sopt : value option -> state
  | Sint : int -> state
  | Sbool : bool -> state
  | Sstate0 : Ident.t -> state
  | Sstate1 : Ident.t * value list -> state
 
type 'a untyped =
  | TypeError : 'a untyped
  | Typed : 'a -> 'a untyped

type 'a uncausal =
  | CausalError : 'a uncausal
  | Causal : 'a -> 'a uncausal

type ('a, 's) costream =
  | CoF : { init : 's;
            step : 's -> ('a * 's) option } -> ('a, 's) costream

type ('a, 'b, 's) node =
  | CoFun  : ('a -> 'b option) -> ('a, 'b, 's) node
  | CoNode : { init : 's;
               step : 's -> 'a -> ('b * 's) option } -> ('a, 'b, 's) node

type gvalue =
  | Gvalue : value -> gvalue
  | Gfun : (value list, value list, state) node -> gvalue
