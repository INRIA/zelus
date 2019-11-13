let warmup = ref 1
let accuracy = ref None
let perf = ref None
let perf_step = ref None
let mem = ref None
let mem_ideal = ref None
let min_particles = ref 1
let max_particles = ref 100
let exp_seq_flag = ref false
let pgf_format = ref false
let mse_target = ref None
let mse_mag = ref 0.5
let increment = ref 1

let select_particle = ref None
let num_runs = ref 10
let seed = ref None
let upper_quantile = 0.9
let lower_quantile = 0.1
let middle_quantile = 0.5


let args =
  Arg.align [
    ("-w", Set_int warmup,
     "n Number of warmup iterations");
    ("-num-runs", Set_int num_runs,
     "n Number of runs");
    ("-acc", String (fun file -> accuracy := Some file),
     "file Accuracy testing" );
    ("-perf", String (fun file -> perf := Some file),
     "file Performance testing");
    ("-perf-step", String (fun file -> perf_step := Some file),
     "file Performance testing on a per step basis");
    ("-mem-step", String (fun file -> mem := Some file),
     " Memory testing on a per step basis");
    ("-mem-ideal-step", String (fun file -> mem_ideal := Some file),
     " Memory testing on a per step basis with GC at each step");
    ("-particles", Int (fun i -> select_particle := Some i),
     "n Number of particles (single run)");
    ("-min-particles", Int (fun i -> min_particles := i),
     "n Lower bound of the particles interval");
    ("-max-particles", Int (fun i -> max_particles := i),
     "n Upper bound of the particles interval");
    ("-exp", Set exp_seq_flag,
     " Exponentioal sequence");
    ("-pgf",  Set pgf_format,
     "PGF Format");
    ("-mse-target", Float (fun f -> mse_target := Some f),
     "n MSE Target value");
    ("-mse-mag", Float (fun f -> mse_mag := f),
     "n Magnitude compared to the MSE Target (log scale)");
    ("-incr", Int (fun i -> increment := i),
     "n Increment in the particles interval");
    ("-seed", Int (fun i -> seed := Some i),
     "n Set seed of random number generator");
  ]

let () =
  Arg.parse args (fun _ -> ()) "particles test harness"

let () =
  begin match !seed with
    | None -> Random.self_init()
    | Some i -> Random.init i
  end

let () =
  begin match !select_particle with
    | Some i -> min_particles := i; max_particles := i
    | None -> ()
  end

let parts = ref !min_particles

let particles _ =
  !parts

let () =
  if !accuracy = None && !perf = None &&
     !mem = None && !mem_ideal = None && !perf_step = None then begin
    Arg.usage args
      "No tests performed: -acc, -perf, -perf-step, -mem-step, or -mem-ideal-step required";
    exit 1
  end
