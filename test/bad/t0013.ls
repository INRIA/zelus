(* pour tester ../../compiler/hyc.byte -i -v -I ../../lib t13.ls *)
(* pour debugger
   set arguments -I ../lib ../test/good/t13.ls *)

let hybrid sliding () = (x, y) where
 rec match y >= 0.0 with
        | true -> do der x= 1.0 and der y = -1.0 done
        | false -> do der x = 1.0 and der y = 1.0 done
    and init x = 1.0 and init y = 1.0
