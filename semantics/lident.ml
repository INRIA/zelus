type t =
  | Name : string -> t
  | Modname : qualident -> t

and qualident = { qual : string; id: string }

let compare = compare

                
