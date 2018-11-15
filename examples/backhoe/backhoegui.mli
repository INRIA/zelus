
(* min, max, initial *)
val leg_range    : float * float * float
val boom_range   : float * float * float
val stick_range  : float * float * float
val bucket_range : float * float * float

type backhoe
val show : unit -> backhoe
val update : backhoe
    -> float    (* leg position *)
    -> float    (* boom angle   *)
    -> float    (* stick angle  *)
    -> float    (* bucket angle *)
    -> bool     (* alarm lamp   *)
    -> bool     (* done lamp    *)
    -> bool     (* cancel lamp  *)
    -> unit

val showupdate :
      float    (* leg position *)
    * float    (* boom angle   *)
    * float    (* stick angle  *)
    * float    (* bucket angle *)
    * bool     (* alarm lamp   *)
    * bool     (* done lamp    *)
    * bool     (* cancel lamp  *)
    -> unit
val showsample : unit -> (bool * bool * bool)

(* retrieve and reset:
 *   stop button, retract button, extend button
 *)
val sample : backhoe -> (bool * bool * bool)
