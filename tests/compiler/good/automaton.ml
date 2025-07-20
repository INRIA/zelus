(* The Zelus compiler, version 2024-dev
  (2025-06-9-16:9) *)
open Ztypes
type ('a) machine_16 = {mutable i_15: 'a}
type ('c, 'b, 'a) machine_14 =
{mutable res_13: 'c; mutable state_12: 'b; mutable o_9: 'a}
type state__255 = One_4 |Two_5 
let (f) =
      let f_8 =
          let machine_14  = 
            
            let machine_14_alloc _ =
              ();
              { res_13 = (false:bool);
                state_12 = (Two_5:state__255); o_9 = ((-1):int) } in
            let machine_14_reset self  =
              ((self.o_9 <- 0; self.res_13 <- false; self.state_12 <- One_4):
              unit) in
            let machine_14_step self _ =
              (((match self.state_12 with
                   | One_4 ->
                       self.o_9 <- (+) self.o_9 1;
                       (match (>=) self.o_9 10 with
                          | true ->
                              self.res_13 <- true; self.state_12 <- Two_5
                          | _ -> self.res_13 <- false )
                   | Two_5 ->
                       self.o_9 <- (-) self.o_9 1;
                       (match (<=) self.o_9 0 with
                          | true ->
                              self.res_13 <- true; self.state_12 <- One_4
                          | _ -> self.res_13 <- false )
                   ); self.o_9):int) in
            Node { alloc = machine_14_alloc; reset = machine_14_reset;
                                             step = machine_14_step } in
            machine_14 in
      f_8
let (main) =
      let main_10 =
          let machine_16  = 
            let Node { alloc = i_15_alloc; step = i_15_step;
                                           reset = i_15_reset } = f  in
            let machine_16_alloc _ =
              ();{ i_15 = i_15_alloc () (* discrete *)  } in
            let machine_16_reset self  =
              (i_15_reset self.i_15 :unit) in
            let machine_16_step self _ =
              ((let o_11 = i_15_step self.i_15 () in
                let _ = print_int o_11 in
                print_newline ()):unit) in
            Node { alloc = machine_16_alloc; reset = machine_16_reset;
                                             step = machine_16_step } in
            machine_16 in
      main_10
