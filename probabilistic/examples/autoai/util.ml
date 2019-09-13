let () = Random.self_init ()

let run_cmd cmd =
  let ch = Unix.open_process_in cmd in
  let n = float_of_string (input_line ch) in
  Format.printf "XXXXXXXXXXX %s accuracy = %f@." cmd n;
  close_in ch;
  n


let oiter f o =
  begin match o with
  | Some x -> f x
  | None -> ()
  end

open Ztypes

type state = { mutable ch : in_channel option }

(* let run_cmd_delay cmd = *)
(*   let alloc () = { ch = None } in *)
(*   let reset state = *)
(*     oiter close_in state.ch; *)
(*     state.ch <- None *)
(*   in *)
(*   let step state cmd = *)
(*     let res = *)
(*       begin match state.ch with *)
(*       | None -> 0. *)
(*       | Some ch -> *)
(*           let x = float_of_string (input_line ch) in *)
(*           close_in ch; *)
(*           x *)
(*       end *)
(*     in *)
(*     state.ch <- Some (Unix.open_process_in cmd); *)
(*     res *)
(*   in *)
(*   let copy src dst = *)
    
(*   in *)
(*   Cnode { alloc; reset; copy; step } *)

let run_cmd_half cmd =
  let alloc () = { ch = None } in
  let reset state =
    oiter close_in state.ch;
    state.ch <- None
  in
  let step state cmd =
    begin match state.ch with
    | None ->
        state.ch <- Some (Unix.open_process_in cmd);
        (4012., false)
    | Some ch ->
        let x = float_of_string (input_line ch) in
        close_in ch;
        (x, true)
    end
  in
  let copy src dst =
    begin match src.ch, dst.ch with
    | None, None -> ()
    | _, _ -> failwith "Do not copy a node with a running command!"
    end
  in
  Cnode { alloc; reset; copy; step }
