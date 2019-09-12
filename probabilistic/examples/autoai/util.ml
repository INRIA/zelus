let run_cmd cmd =
  let ch = Unix.open_process_in cmd in
  let n = float_of_string (input_line ch) in
  close_in ch;
  n
