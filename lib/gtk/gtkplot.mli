
type signal_type =
  | Points of bool
  | PiecewiseContinuous of bool
  | LinearInterpolation

val points  : bool -> signal_type
val piecewise : signal_type (* PiecewiseContinuous false *)
val square    : signal_type (* PiecewiseContinuous true  *)
val linear    : signal_type

type signal
type scope
type window

val getSignals:
  (string
  * signal_type
  * 'a) list
  -> (string * signal_type) list
val getValues:
  ('a
  * 'b
  * float) list
  -> float list

val signal :
     string         (* name *)
  * signal_type    (* type of plot *)
  -> signal

val signal_l :
     (string         (* name *)
  * signal_type)     (* type of plot *)
     list
  -> signal list

(* must have called allocate_signals first *)
val update : signal * float -> unit
val update_l : signal list * float list -> unit

(* A signal must only be added to a single scope *)
val scope :
     float       (* minimum on y_axis *)
  * float       (* maximum on y_axis *)
  * signal list
  -> scope

(* A scope must only be added to a single window *)
val window :
     string (* window title *)
  * float  (* initial maximum time *)
  * scope list
  -> window

val tick :
     window
  * float  (* current time *)
  -> unit
