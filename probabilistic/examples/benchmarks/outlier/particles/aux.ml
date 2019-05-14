open Infer_ds;;

let warmup = ref 0 ;;
let perf = ref false;;
let perf_step = ref false;;
let mem = ref false;;
let select_particle = ref None;;

Arg.parse[
    ("-w", Set_int warmup, "Numberof warmup iterations"); 
    ("-perf", Unit (fun _ -> perf := true), "Performance testing");
    ("-perf-step", Unit (fun _ -> perf_step := true), "Performance testing on a per step basis");
    ("-mem", Unit (fun _ -> mem := true), "Memory performance testing");
    ("-particles", Int (fun i -> select_particle := Some i), "Number of particles (single run)")
] (fun _ -> ()) "Kalman particles test harness";;

let parts = ref 
    begin match !select_particle with
    | Some i -> i
    | None -> 10
    end
;;

let particles _ =
    !parts
;;


(*
let read_val : unit -> (float * float) option =
    fun _ ->
    try
        Scanf.scanf "%f, %f\n" (fun t o -> Some (t, o))
    with End_of_file -> None
;;
*)

let read_val : unit ->  float * float =
    fun _ ->
        Scanf.scanf "%f, %f\n" (fun t o -> (t, o))
;;

let get_mean (type a) : (bool * float) Distribution.t -> float =
    fun d ->
        begin match d with
        | Distribution.Dist_support sup ->
            let rec avg lst =
                begin match lst with
                | [] -> 0.
                | ((_, v), p) :: rst ->
                    (v *. p) +. (avg rst)
                end
            in
            avg sup
        | _ -> assert false
        end
;;

let particles_tostring (type a) : (bool * float) Distribution.t -> string =
    fun d ->
        begin match d with
        | Distribution.Dist_support sup ->
            let rec str lst =
                begin match lst with
                | [] -> ""
                | ((outl, v), p) :: rst ->
                    ("(" ^ (string_of_bool outl) ^ ", " ^ (string_of_float v ^", " ^ (string_of_float p) ^ "); " ^ (str rst)))
                end
            in
            str sup
        | _ -> assert false
        end
;;
 

let random_init : unit -> unit =
    fun _ ->
        Random.self_init ()
;;

let collect_garbage : unit -> unit =
    fun _ -> (*Gc.full_major ()*)()
;;

let get_memory : unit -> float =
    fun _ ->
        (*let st = Gc.stat () in
        float_of_int st.live_words*)
        0.0
;;

let get_time : unit -> float =
    fun _ ->
        (*Sys.time ()*)0.0
;;
