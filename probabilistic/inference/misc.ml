let rec list_replace_assoc x f l =
  begin match l with
    | [] -> [ (x, f None) ]
    | (y, v) :: l ->
      if x = y then
        (x, f (Some v)) :: l
      else
        (y, v) :: list_replace_assoc x f l
  end
