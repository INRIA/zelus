type t =
  | Name : string -> t
  | Modname: { qual : t; id: string } -> t

let compare = compare

                
