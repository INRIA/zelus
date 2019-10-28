open Core
open Stdio

let file = "german.data"
let ic_german = In_channel.create file

type value = int array

let value_of_string line =
  let s = Str.(split (regexp " +") line) in
  let v = Array.create ~len:(List.length s) (-1) in
  List.iteri
    s
    ~f:(fun i a ->
        if a.[0] = 'A' then begin
          let pfx_len = 1 + String.length (Int.to_string (i + 1)) in
          v.(i) <- Int.of_string (String.drop_prefix a pfx_len)
        end else
          v.(i) <- Int.of_string a);
  v

type gender = Male | Female

let gender v =
  begin match v.(8) with
    | 1 | 3 | 4 -> Male
    | 2 | 5     -> Female
    | _         -> assert false
  end

type status = Good | Bad

let status v =
  begin match v.(20) with
    | 1 -> Good
    | 2 -> Bad
    | _ -> assert false
  end


let readline () =
  begin match In_channel.input_line ic_german with
    | Some line -> value_of_string line
    | None -> In_channel.close ic_german; exit 0
  end


let printline () =
  let v = readline () in
  begin match gender v with
    | Male   -> Format.printf "Male "
    | Female -> Format.printf "Female "
  end;
  begin match status v with
    | Good -> Format.printf "Good "
    | Bad  -> Format.printf "Bad "
  end;
  Format.printf "@.";
  Out_channel.flush stdout


let () =
  printline ();
  printline ();
  printline ();
  printline ();