(* Printing a location in the source program *)
(* taken from the source of the Caml Light 0.73 compiler *)


open Format

(* two important global variables: [input_name] and [input_chan] *)
type location =
    Loc of int     (* Position of the first character *)
         * int     (* Position of the next character following the last one *)



let input_name = ref ""                 (* Input file name. *)

let input_chan = ref stdin

let initialize iname =
  input_name := iname;
  input_chan := open_in iname


let no_location =  Loc(0,0)


let error_prompt = ">"

let output_lines ff char1 char2 charline1 line1 line2 =
  let n1 = char1 - charline1
  and n2 = char2 - charline1 in
    if line2 > line1 then
      fprintf ff
        ", line %d-%d, characters %d-%d:\n" line1 line2 n1 n2
    else
      fprintf ff ", line %d, characters %d-%d:\n" line1 n1 n2;
    ()


let output_loc ff input seek line_flag (Loc(pos1, pos2)) =
  let pr_chars n c =
    for i = 1 to n do pp_print_char ff c done in
  let skip_line () =
    try
      while input() != '\n' do () done
    with End_of_file -> () in
  let copy_line () =
    let c = ref ' ' in
      begin try
        while c := input(); !c != '\n' do pp_print_char ff !c done
      with End_of_file ->
        pp_print_string ff "<EOF>"
      end;
      pp_print_char ff '\n' in
  let pr_line first len ch =
    let c = ref ' '
    and f = ref first
    and l = ref len in
      try
        while c := input (); !c != '\n' do
          if !f > 0 then begin
            f := !f - 1;
            pp_print_char ff (if !c == '\t' then !c else ' ')
          end
          else if !l > 0 then begin
            l := !l - 1;
            pp_print_char ff (if !c == '\t' then !c else ch)
          end
          else ()
        done
      with End_of_file ->
        if !f = 0 && !l > 0 then pr_chars 5 ch in
  let pos = ref 0
  and line1 = ref 1
  and line1_pos = ref 0
  and line2 = ref 1
  and line2_pos = ref 0 in
  seek 0;
  begin try
    while !pos < pos1 do
      incr pos;
      if input() == '\n' then begin incr line1; line1_pos := !pos; () end
    done
  with End_of_file -> ()
  end;
  line2 := !line1;
  line2_pos := !line1_pos;
  begin try
    while !pos < pos2 do
      incr pos;
      if input() == '\n' then
        begin incr line2; line2_pos := !pos; () end
    done
  with End_of_file -> ()
  end;
  if line_flag then output_lines ff pos1 pos2 !line1_pos !line1 !line2;
  if !line1 == !line2 then begin
    seek !line1_pos;
    pp_print_string ff error_prompt;
    copy_line ();
    seek !line1_pos;
    pp_print_string ff error_prompt;
    pr_line (pos1 - !line1_pos) (pos2 - pos1) '^';
    pp_print_char ff '\n'
  end else begin
    seek !line1_pos;
    pp_print_string ff error_prompt;
    pr_line 0 (pos1 - !line1_pos) '.';
    seek pos1;
    copy_line();
    if !line2 - !line1 <= 8 then
      for i = !line1 + 1 to !line2 - 1 do
        pp_print_string ff error_prompt;
        copy_line()
      done
    else
      begin
        for i = !line1 + 1 to !line1 + 3 do
          pp_print_string ff error_prompt;
          copy_line()
        done;
        pp_print_string ff error_prompt; pp_print_string ff "..........\n";
        for i = !line1 + 4 to !line2 - 4 do skip_line() done;
        for i = !line2 - 3 to !line2 - 1 do
          pp_print_string ff error_prompt;
          copy_line()
        done
      end;
    begin try
      pp_print_string ff error_prompt;
      for i = !line2_pos to pos2 - 1 do
        pp_print_char ff (input())
      done;
      pr_line 0 100 '.'
    with End_of_file -> pp_print_string ff "<EOF>"
    end;
    pp_print_char ff '\n'
  end


let output_location ff loc =
  let p = pos_in !input_chan in
  fprintf ff "File \"%s\"" !input_name;
  output_loc
    ff (fun () -> input_char !input_chan) (seek_in !input_chan) true
    loc;
  seek_in !input_chan p


let output_input_name ff =
  fprintf ff "File \"%s\", line 1:\n" !input_name

