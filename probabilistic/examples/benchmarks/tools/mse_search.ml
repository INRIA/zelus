open Benchlib

module Config = struct

  let file = ref None
  let mse_target = ref 0.1
  let mse_mag = ref 0.5
  let pgf_format = ref false

  let args =
    Arg.align [
      ("-pgf",  Set pgf_format,
       "PGF Format");
      ("-mse-target", Float (fun f -> mse_target := f),
       "n MSE Target value");
      ("-mse-mag", Float (fun f -> mse_mag := f),
       "n Magnitude compared to the MSE Target (log scale)");
      ]

    let () =
      Arg.parse args (fun f -> file := Some f) "search target mse"

end

let search mse_target mag stats =
  List.find
    (fun (_, (_, _, mse)) ->
       let r = abs_float (log10 mse -. log10 mse_target) in
       r <= mag
    )
    (Array.to_list stats)


let main =
  let file =
    begin match !Config.file with
    | Some f -> f
    | None -> assert false
    end
  in
  let stats = Stats.read_stats file in
  begin match search !Config.mse_target !Config.mse_mag stats with
  | particles, (low, mid, high) ->
      Format.printf "%s (target %f): number of particles = %d@."
        file !Config.mse_target particles;
      Format.printf "\tmse: %f %f %f@."
        low mid high
  | exception Not_found ->
      let particles, (_, _, mse) = stats.(Array.length stats - 1) in
      let r = abs_float (log10 mse -. log10 !Config.mse_target) in
      Format.printf "%s: %d particles is not enough (%f > %f).@."
        file particles r !Config.mse_mag
  end
