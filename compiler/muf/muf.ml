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

type core_type =
  | Tany
  | Tvar of string
  | Ttuple of core_type list
  | T_constr of string * core_type list
[@@deriving show, map, fold]

type 'p patt_desc =
  | Pid of identifier
  | Pconst of constant
  | Ptuple of 'p list
  | Ptype of 'p * core_type
  | Pany
[@@deriving show, map, fold]

type 'm pattern =
  { patt: 'm pattern patt_desc; pmeta: 'm }
[@@deriving show, map, fold]

type ('pattern, 'expr) expr_desc =
  | Econst of constant
  | Econstr of identifier * 'expr option
  | Evar of identifier
  | Etuple of 'expr list
  | Erecord of (string * 'expr) list * 'expr option
  | Efield of 'expr * string
  | Eapp of 'expr * 'expr
  | Eif of 'expr * 'expr * 'expr
  | Ematch of 'expr * ('pattern, 'expr) case list
  | Elet of 'pattern * 'expr * 'expr
  | Esequence of 'expr * 'expr
  | Ecall_init of 'expr
  | Ecall_step of 'expr * 'expr (* instance is: (identifier * string option) *)
  | Ecall_reset of 'expr        (* instance is: (identifier * string option) *)
  | Esample of prob * 'expr
  | Eobserve of prob * 'expr * 'expr
  | Efactor of prob * 'expr
  | Einfer of 'expr * identifier
[@@deriving show, map, fold]

and prob = string
[@@deriving show]

and ('pattern, 'expr) case =
  { case_patt: 'pattern; case_expr: 'expr; }
[@@deriving show, map, fold]

type 'm expression =
  { expr: ('m pattern, 'm expression) expr_desc; emeta: 'm }
[@@deriving show, map, fold]

type type_kind =
  | TKrecord of (string * core_type) list
[@@deriving show, map, fold]

type ('p, 'e) node =
  { n_type : string list * type_kind;
    n_init : 'e;
    n_step : 'p * 'e; }
[@@deriving show, map, fold]

type ('p, 'e) decl_desc =
  | Ddecl of 'p * 'e
  | Dfun of identifier * 'p * 'e
  | Dnode of identifier * 'p list * ('p, 'e) node
  | Dtype of identifier * string list * type_kind
  | Dopen of string
[@@deriving show, map, fold]

type 'm declaration =
  { decl: ('m pattern, 'm expression) decl_desc }
[@@deriving show, map, fold]

type 'm program =
   'm declaration list
[@@deriving show]
