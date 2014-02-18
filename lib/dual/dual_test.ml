(* Run with ./ocaml_dual *)

(* Basics tests *)

let x = Dual.make 2. 1.;;

assert ((Dual.re x) = 2.);;
assert ((Dual.im x) = 1.);;

let y = Dual.make 2. 3.;;

assert ((Dual.re y) = 2.);;
assert ((Dual.im y) = 3.);;

assert (x = y);;

let z = Dual.( *. ) x y;;

assert ((Dual.re z) = (Pervasives.( *. ) (Dual.re x) (Dual.re y)));;
assert
  ((Dual.im z) =
      (Pervasives.(+.)
	  (Pervasives.( *. ) (Dual.re x) (Dual.im y))
	  (Pervasives.( *. ) (Dual.im x) (Dual.re y))));;

let z = Dual.(+.) x y;;

assert ((Dual.re z) = (Pervasives.( +. ) (Dual.re x) (Dual.re y)));;
assert ((Dual.im z) = (Pervasives.( +. ) (Dual.im x) (Dual.im y)));;

let pi = Pervasives.( *. ) 4. (Pervasives.atan 1.);;

let z = Dual.cos (Dual.make pi 1.);;

Dual.re z;;
Dual.im z;;

assert ((Pervasives.(+.) (Pervasives.( *. ) (Dual.re z) (Dual.re z)) (Pervasives.( *. ) (Dual.im z) (Dual.im z))) = 1.);;

let z = Dual.cos (Dual.make (Pervasives.(/.) pi 4.) 1.);;

Dual.re z;;
Dual.im z;;

assert ((Pervasives.abs_float (Pervasives.(-.) (Pervasives.( *. ) (Dual.re z) (Dual.re z)) (Pervasives.( *. ) (Dual.im z) (Dual.im z)))) <= 1.e-15);;

(* More involved test *)

open Pervasives__dual;;

type p = { x : float; y : float };;

let revolve r omega t =
  {
    x = r *. (cos (omega *. t));
    y = r *. (sin (omega *. t))
  };;

let dis { x=x; y=y } = sqrt ((x *. x) +. (y *. y));;

let sample = List.map (fun t -> Dual.make t 1.) [ 0.; 1.; 2.; 3.; 4.; 5.; 6.; 7.; 8.; 9. ];;

let r = Dual.make 1. 0.;;

let omega = Dual.make 1. 0.;;

let der = List.map (fun t -> Dual.im (dis (revolve r omega t))) sample;;

assert (List.for_all ((=) 0.) der);;

(* Testing comparison relations *)

let zero = Dual.const 0.
and one = Dual.const 1.;;

assert ((compare zero one) = (compare 0 1));;
assert ((compare one one) = (compare 1 1));;
assert ((compare one zero) = (compare 1 0));;

assert ((compare neg_infinity zero) = (compare Pervasives.neg_infinity 0.));;
assert
  ((compare
       (one /. neg_infinity)
       (one /. infinity)) =
      (compare
	  (Pervasives.(/.) 1. Pervasives.neg_infinity)
	  (Pervasives.(/.) 1. Pervasives.infinity)));;

assert ((compare nan neg_infinity) = (compare Pervasives.nan Pervasives.neg_infinity));;

(* Testing the Newton-Raphson solver *)

let g x y = (dis { x=x; y=y }) -. (Dual.const 1.);;

let eps =  1.e-12;;

let my_solver = Newton.solve eps 1.;;

let x = Dual.inv (sqrt (Dual.const 2.));;

let y0 = 0.5;;

let y = Dual.const (my_solver (g x) y0) ;;

assert ((Dual.re (g x y)) <= eps);;

(* Testing implicit function of 1 parameter *)

let f x = Implicit.implicit1 my_solver g x (Dual.const y0);;

List.iter
  (fun x ->
    let y = f x in
      Printf.printf "f(%s)=%s\n" (Dual.string_of_dual x) (Dual.string_of_dual y))
  (List.map (fun x0 -> Dual.make x0 1.) [0.; 0.1; 0.2; 0.3; 0.4; 0.5; 0.6; 0.7; 0.8; 0.9]);;

(* Testing implicit function of 2 parameters *)

let h a b c = (cos a) *. (cos b) *. c -. (Dual.const 1.);;

let f a b = Implicit.implicit2 my_solver h a b (Dual.const 1.);;

Dual.re (f (Dual.const 1.) (Dual.const 1.));;
Dual.re (f (Dual.const 0.5) (Dual.const 0.5));;
Dual.im (f (Dual.make 0.5 1.) (Dual.const 0.5));;

(* Testing the Gauss-Newton solver *)

let my_solver2 = Newton.solve2 eps 2.;;

let x0 = 0.59
and y0 = 0.61;;

let (x,y) = my_solver2 g x0 y0;;

assert ((Dual.re (g (Dual.const x) (Dual.const y))) <= eps);;

my_solver2 g 0. 0.9;;
my_solver2 g 1.1 0.;;
my_solver2 g 0.001 (-0.001);;
