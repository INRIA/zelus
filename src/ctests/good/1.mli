type t

type 'a t'

type 'a t'' = A of t | B | C of int * int t''

val f : int -> int

val g : int -> int -> int

val h : (int -> int -D-> int) -D-> (int -V-> int) -> (int -S-> (int * int))
