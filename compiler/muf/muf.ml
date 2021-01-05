type constant =
  | Cbool of bool
  | Cint of int
  | Cint32 of int32
  | Cint64 of int64
  | Cfloat of string
  | Cstring of string
  | Cchar of char
  | Cunit
  | Cany
[@@deriving show]

type identifier =
  { name: string }
[@@deriving show, map, fold]

type 'p patt_desc =
  | Pid of identifier
  | Ptuple of 'p list
  | Pany
[@@deriving show, map, fold]

type 'm pattern =
  { patt: 'm pattern patt_desc; pmeta: 'm }
[@@deriving show, map, fold]

type ('pattern, 'expr) expr_desc =
  | Econst of constant
  | Evar of identifier
  | Etuple of 'expr list
  | Erecord of (string * 'expr) list * 'expr option
  | Efield of 'expr * string
  | Eapp of 'expr * 'expr
  | Eif of 'expr * 'expr * 'expr
  | Elet of 'pattern * 'expr * 'expr
  | Esequence of 'expr * 'expr
  | Esample of 'expr
  | Eobserve of 'expr * 'expr
  | Efactor of 'expr
  | Einfer of ('pattern * 'expr) * 'expr
[@@deriving show, map, fold]

type 'm expression =
  { expr: ('m pattern, 'm expression) expr_desc; emeta: 'm }
[@@deriving show, map, fold]

type core_type =
  | Tany
  | Tvar of string
  | Ttuple of core_type list
  | T_constr of string * core_type list
[@@deriving show, map, fold]

type type_kind =
  | TKrecord of (string * core_type) list
[@@deriving show, map, fold]

type ('p, 'e) decl_desc =
  | Ddecl of 'p * 'e
  | Dfun of identifier * 'p * 'e
  | Dtype of identifier * string list * type_kind
[@@deriving show, map, fold]

type 'm declaration =
  { decl: ('m pattern, 'm expression) decl_desc }
[@@deriving show, map, fold]

type 'm program =
   'm declaration list
[@@deriving show]
