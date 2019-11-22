open Benchlib

module Config = struct

  let file = ref None
  let perf_target = ref 0.1
  let pgf_format = ref false

  let args =
    Arg.align [
      ("-target", Float (fun f -> perf_target := f),
       "n Target value");
      ]

    let () =
      Arg.parse args (fun f -> file := Some f) "search target latency"

end

let search target stats =
  let n_res = ref 0 in
  List.iter
    (fun (n, (_, obs, _)) -> if obs <= target +. epsilon_float then n_res := n)
    (Array.to_list stats);
  !n_res

let main =
  let file =
    begin match !Config.file with
    | Some f -> f
    | None -> assert false
    end
  in
  let stats = Stats.read_stats file in
  let n = search !Config.perf_target stats in
  Format.printf "%s (target %f): number of particles = %d@."
    file !Config.perf_target n
