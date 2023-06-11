
type airtraffic

val show :
     float        (* d, the distance to deviate for avoidance, in miles *)
  -> float        (* dtheta, the change in heading for avoidance, radians *)
  -> float        (* alert radius in miles *)
  -> float        (* protected radius in miles (protected < alert ) *)
  -> float        (* incorporate delta_phi into animation (set to 0.0 to ignore) *)
  -> airtraffic

val update :
  airtraffic
  -> int        (* state: 0=Cruising, 1=Left, 2=Straight, 3=Right *)
  -> float      (* relative x-coordinate of aircraft2, miles *)
  -> float      (* relative y-coordinate of aircraft2, miles *)
  -> float      (* relative rotation of aircraft2, radians *)
  -> float      (* velocity of aircraft1, miles/hour *)
  -> float      (* velocity of aircraft2, miles/hour *)
  -> float      (* value of timer used in avoidance algorithm, seconds *)
  -> unit

val sample :
  (* airtraffic *) unit
  -> bool               (* clicked or not *)
     * (float * float)  (* x, y *)
     * (float * float)  (* angle, length *)

val showupdate:
    float        (* d, the distance to deviate for avoidance, in miles *)
  * float        (* dtheta, the change in heading for avoidance, radians *)
  * float        (* alert radius in miles *)
  * float        (* protected radius in miles (protected < alert ) *)
  * float        (* incorporate delta_phi into animation (set to 0.0 to ignore) *)

  * int          (* state: 0=Cruising, 1=Left, 2=Straight, 3=Right *)
  * float        (* relative x-coordinate of aircraft2, miles *)
  * float        (* relative y-coordinate of aircraft2, miles *)
  * float        (* relative rotation of aircraft2, radians *)
  * float        (* velocity of aircraft1, miles/hour *)
  * float        (* velocity of aircraft2, miles/hour *)
  * float        (* value of timer used in avoidance algorithm, seconds *)
  -> unit

