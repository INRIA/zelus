let warmup = ref 0 ;;
let perf = ref false;;
let perf_step = ref false;;
let mem = ref false;;
let select_particle = ref None;;

let () =
  Arg.parse[
    ("-w", Set_int warmup, "Numberof warmup iterations");
    ("-perf", Unit (fun _ -> perf := true), "Performance testing");
    ("-perf-step", Unit (fun _ -> perf_step := true), "Performance testing on a per step basis");
    ("-mem", Unit (fun _ -> mem := true), "Memory performance testing");
    ("-particles", Int (fun i -> select_particle := Some i), "Number of particles (single run)")
  ] (fun _ -> ()) "test harness"

let parts =
  ref
    begin match !select_particle with
      | Some i -> i
      | None -> 10
    end

let particles _ =
  !parts
