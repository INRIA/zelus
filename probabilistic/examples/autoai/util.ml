let run_cmd cmd =
  let ch = Unix.open_process_in cmd in
  let n = float_of_string (input_line ch) in
  Format.printf "XXXXXXXXXXX %s accuracy = %f@." cmd n;
  close_in ch;
  n
