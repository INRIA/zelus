
(* --[[ TYPE DEFINITION *)
type value =
  | Vsig of bool
  | Vbool of bool
  | Vint of int
  | Vfloat of float

type input_type =
  | Sig
  | Bool of bool
  | Int of (int * int) * int
  | Float of (float * float) * float

type input_desc = string * input_type

type input_win =
  | Inp of input_desc
  | Frame of string * input_win
  | HBox of input_win list
  | VBox of input_win list
(* --]]*)
(* --[[ UTILS *)
let short_string_of_input_type = function
  | Sig -> "sig"
  | Bool _ -> "bool"
  | Int _ -> "int"
  | Float _ -> "float"

let string_of_input_type = function
  | Sig -> "sig"
  | Bool b -> "bool (" ^ (string_of_bool b) ^ ")"
  | Int ((i1, i2), default) ->
    "int[" ^ (string_of_int i1) ^ ", "
           ^ (string_of_int i2) ^ "] "
      ^ "(" ^ (string_of_int default) ^ ")"
  | Float ((f1, f2), default) ->
    "float[" ^ (string_of_float f1) ^ ", "
             ^ (string_of_float f2) ^ "] "
        ^ "(" ^ (string_of_float default) ^ ")"

let type_of_value = function
  | Vsig _ -> "sig"
  | Vbool _ -> "bool"
  | Vint _ -> "int"
  | Vfloat _ -> "float"

let string_of_value = function
  | Vsig b -> if b then "Present" else "Absent"
  | Vbool b -> string_of_bool b
  | Vint i -> string_of_int i
  | Vfloat f -> string_of_float f

let string_of_input_desc (s, ty) = s ^ " : " ^ (short_string_of_input_type ty)

(* Get the list of all variables defined in win*)
let get_inputs win =
  let rec aux = function
    | Inp i -> [i]
    | Frame (_, w) -> aux w
    | HBox w_l -> List.flatten (List.map aux w_l)
    | VBox w_l -> List.flatten (List.map aux w_l)
  in
  aux win
(* --]]*)
(* --[[ INPUT *)
(* The input class draws the right widget (depending on the type `typ` of the
 * input) and updates the environment `env` (at initalization and each time
 * the widget fires events).
 * It uses `packing` to pack the widget. *)
class input (env : (string, value) Hashtbl.t)
    (packing : GObj.widget -> unit) ((name, typ) : input_desc)  =
  object (self)

    method private init_val v =
      (* check if the name `name` is already used in the environment *)
      if Hashtbl.mem env name then begin
        Printf.eprintf "Variable %s has been declared twice\n" name;
        exit 1
      end;
      self#set_val v

    method private set_val v =
      (* check that v has the right type *)
      ignore (match typ, v with
      | Sig, Vsig _
      | Bool _, Vbool _
      | Int _, Vint _
      | Float _, Vfloat _ -> ()
      | _ -> Printf.eprintf "Variable %s has type %s but is assigned with a value of type %s."
               name (short_string_of_input_type typ) (type_of_value v);
        exit 1 );
      Hashtbl.add env name v;

    method private make_widget () =
      match typ with
      | Sig                       -> self#make_sig   packing
      | Bool default              -> self#make_bool  packing default
      | Int ((i1, i2), default)   -> self#make_int   packing (i1, i2) default
      | Float ((f1, f2), default) -> self#make_float packing (f1, f2) default

    (* Button *)
    method private make_sig packing =
      let widget = GButton.button ~label:("Trigger " ^ name) ~packing:packing () in
      (* connect callback *)
      ignore (widget#connect#clicked ~callback:(fun () -> self#set_val (Vsig true)));
      self#init_val (Vsig false)

    (* Checkbox *)
    method private make_bool packing default =
      let widget = GButton.check_button  ~label:(string_of_input_desc (name, typ))
          ~active:default ~packing:packing () in
      (* connect callback *)
      ignore (widget#connect#toggled ~callback:(fun () -> self#set_val (Vbool widget#active)));
      self#init_val (Vbool default)

    (* Frame with a scale inside *)
    method private make_int packing (i1, i2) default =
      let get_label v = Printf.sprintf "%s = %d" name v in
      let frame = GBin.frame ~label:(get_label default)
          ~packing:packing () in

      (* There is a weird bug with GRange.scale: if the interval [lower, upper]
       * is too small, the scale widget doesn't work properly.
       * To reproduce the bug, run the following code:
       *
         let _ =
           GMain.init ();

           let screen = Gdk.Screen.default () in
           let width = truncate (float (Gdk.Screen.width  ~screen:screen ()) *. 0.1) in

           let w = GWindow.window ~title:"test" ~width:width () in

           let adj = GData.adjustment
             ~lower:0.
             ~upper:5. (* <-- change this value to something bigger
                        * (like 100.) to make it work *)
             ~value:1.
             ~step_incr:1.0
             () in
           ignore(GRange.scale `HORIZONTAL ~adjustment:adj ~draw_value:true
                  ~value_pos:`LEFT ~digits:0 ~packing:w#add ());

           ignore (w#connect#destroy ~callback:GMain.Main.quit);
           ignore (w#misc#connect#show ~callback:w#show);
           w#set_allow_shrink true;
           w#show ();

           GMain.Main.main()
      *)
      let step_incr = 100.0 in
      let lower = float_of_int (100 * i1) in
      let upper = float_of_int (100 * i2 + 100) in
      let value = float_of_int (100 * default) in
      let adj = GData.adjustment
          ~lower:lower ~upper:upper ~value:value ~step_incr:step_incr () in
      (* create scale widget *)
      ignore(GRange.scale `HORIZONTAL ~adjustment:adj ~draw_value:false
               ~packing:frame#add ());
      (* connect callback *)
      ignore (adj#connect#value_changed
                (fun () ->
                   let new_val = truncate (adj#value /. 100.) in
                   frame#set_label (Some (get_label new_val));
                   self#set_val (Vint new_val)));

      self#init_val (Vint default)

    (* Frame with a scale inside*)
    method private make_float packing (f1, f2) default =
      let get_label v =
        if (v > -10000. && v < -0.01 )
        || (v > 0.01    && v < 10000.)
        || v = 0. then
          Printf.sprintf "%s = %.2f" name v
        else
          (* use scientific notation *)
          Printf.sprintf "%s = %.2e" name v
      in
      let frame = GBin.frame ~label:(get_label default)
          ~packing:packing () in

      (* refer to make_int for weird GRange.scale bug*)
      let step_incr = min 1. (f2 -. f1) in
      let lower = 100. *. f1 in
      let upper = 100. *. f2 +. 10. in
      let value = 100. *. default in
      let adj = GData.adjustment
          ~lower:lower ~upper:upper ~value:value ~step_incr:step_incr () in
      (* create scale widget *)
      ignore(GRange.scale `HORIZONTAL ~adjustment:adj ~draw_value:false
               ~packing:frame#add ());
      (* connect callback *)
      ignore (adj#connect#value_changed
                (fun () ->
                   let new_val = (adj#value /. 100.) in
                   frame#set_label (Some (get_label new_val));
                   self#set_val (Vfloat new_val)));

      self#init_val (Vfloat default)

    initializer
      self#make_widget ()
  end

class window (title : string) (win : input_win) =
  let inputs = get_inputs win in
  let n_inputs = List.length inputs in
  let env = Hashtbl.create n_inputs in

  object (self)

    val w = GWindow.window ~title:title ~allow_shrink:false ()

    method private make_window packing = function
      | Inp i ->
        ignore(new input env packing i)
      | Frame (s, w) ->
        let frame = GBin.frame ~label:s ~packing:packing () in
        let align = GBin.alignment ~padding:(10, 10, 10, 10) ~packing:frame#add () in
        self#make_window align#add w
      | HBox (w_l) ->
        let hbox = GPack.hbox ~homogeneous:true ~spacing:20 ~packing:packing () in
        List.iter (self#make_window hbox#pack) w_l
      | VBox (w_l) ->
        let vbox = GPack.vbox ~spacing:20 ~packing:packing () in
        List.iter (self#make_window vbox#pack) w_l

    method private get_value name =
      try
        Hashtbl.find env name
      with Not_found ->
        Printf.eprintf "The value identifier %s is unbound\n"
          name; exit 1

    method get_sig name =
      match self#get_value name with
      | Vsig s ->
        if s then begin Hashtbl.add env name (Vsig false); true end else false
      | v ->
        Printf.eprintf "Cannot access variable (%s : %s) with method get_sig\n"
          name (type_of_value v); exit 1
    method get_bool name =
      match self#get_value name with
      | Vbool b -> b
      | v ->
        Printf.eprintf "Cannot access variable (%s : %s) with method get_bool\n"
          name (type_of_value v); exit 1
    method get_int name =
      match self#get_value name with
      | Vint i -> i
      | v ->
        Printf.eprintf "Cannot access variable (%s : %s) with method get_int\n"
          name (type_of_value v); exit 1
    method get_float name =
      match self#get_value name with
      | Vfloat f -> f
      | v ->
        Printf.eprintf "Cannot access variable (%s : %s) with method get_float\n"
          name (type_of_value v); exit 1

    method resize width height =
      w#resize ~width:width ~height:height

    initializer
      let align = GBin.alignment ~padding:(10, 10, 10, 10) ~packing:w#add () in

      self#make_window align#add win;

      ignore (w#connect#destroy ~callback:GMain.Main.quit);
      ignore (w#misc#connect#show ~callback:w#show);
      w#show ()
  end

(* INTERFACE*)

let make_sig   s              = Inp (s, Sig)
let make_bool  s b            = Inp (s, Bool b)
let make_int   s (i1, i2) def = Inp (s, Int ((i1, i2), def))
let make_float s (f1, f2) def = Inp (s, Float ((f1, f2), def))

let frame s w = Frame (s, w)
let hbox  w_l = HBox w_l
let vbox  w_l = VBox w_l

let get_sig   (w, s)  = ((), w#get_sig s)
let get_bool  (w, s)  = w#get_bool s
let get_int   (w, s)  = w#get_int s
let get_float (w, s)  = w#get_float s

let resize_window (w, width, height) = w#resize width height
let open_window (title, win) = new window title win

(* (* TEST *)

  let _ =
  let _ = GMain.init () in (* initialize lablgtk2 *)

  let test_window =
    Frame ("Main",
           VBox [ HBox [ Inp ("e", Sig); Inp ("f", Sig); Inp ("g", Sig) ];
                  Frame ("Some floats",
                         HBox [ Inp ("x", Float ((0.0, 9.0), 1.0)); Inp ("y", Float ((0., 90.), 3.))]);
                  Frame ("Some booleans",
                         HBox [ Inp ("b1", Bool true); Inp ("b2", Bool true); Inp ("b3", Bool true) ]);
                  HBox [ Inp ("x1", Int ((0, 100), 1)); Inp ("y1", Int ((1, 90), 3))]
                ]; )
  in

  let w = new window test_window in

  GMain.Main.main (); *)
