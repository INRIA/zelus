(* Set of values *)
(* noinitialized value *)

type 'a uninit =
  | Vinitialized : 'a -> 'a uninit
  | Vnil : 'a -> 'a uninit

(* undefined value *)
type 'a uncausal =
  | Value : 'a -> 'a uncausal
  | Vbot : 'a uncausal

type 'a extended = 'a uninit uncausal


type value =
  | Vint : int -> value
  | Vbool : bool -> value
  | Vfloat : float -> value
  | Vchar : char -> value
  | Vstring : string -> value
  | Vvoid : value
  | Vconstr0 : Lident.t -> value
  | Vtuple : value list -> value
  | Vbot : value
  | Vnil : value
  
type state =
  | Sempty : state
  | Stuple : state list -> state
  | Sval : value -> state
  | Sopt : value option -> state
  | Sbool : bool -> state
  | Sstate0 : Ident.t -> state
  | Sstate1 : Ident.t * value list -> state
 
                
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
