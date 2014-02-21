let node f(t) = (x,y, r, z) where
  rec match t with
      | true -> do y = last x done
      | false -> do x = last y done
  and init y = 0 and init x = 0
  and r = x + 1
and z = y + 2
