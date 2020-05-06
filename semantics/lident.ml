type t =
  | Name : string -> t
  | Modname : qualident -> t

and qualident = { qual : string; id: string }

let compare = compare

let qualidname { qual = m; id = id } = m ^ "." ^ id

let modname = function
  | Name(n) -> n
  | Modname(qualid) -> qualidname qualid

let source = function
  | Name(n) -> n
  | Modname(qualid) -> qualid.id

let fprint_t ff id = Format.fprintf ff "%s" (modname id)
      
