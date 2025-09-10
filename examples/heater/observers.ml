(* The Zelus compiler, version 2.2-dev
  (2021-11-2-11:45) *)
open Ztypes
type ('c , 'b , 'a) _oscillate =
  { mutable i_69 : 'c ; mutable m_67 : 'b ; mutable m_65 : 'a }

let oscillate  = 
  
  let oscillate_alloc _ =
    ();
    { i_69 = (false:bool) ;
      m_67 = (Obj.magic ():'a) ; m_65 = (Obj.magic ():'a) } in
  let oscillate_reset self  =
    (self.i_69 <- true:unit) in 
  let oscillate_step self (x_62:'a651) =
    (((if self.i_69 then self.m_65 <- x_62) ;
      (if self.i_69 then self.m_67 <- x_62) ;
      self.i_69 <- false ;
      (let (x_66:'a651) = self.m_65 in
       self.m_65 <- x_62 ;
       (let (x_68:'a651) = self.m_67 in
        self.m_67 <- x_66 ; (&&) ((<>) x_62  x_66)  ((<>) x_66  x_68)))):
    bool) in
  Node { alloc = oscillate_alloc; reset = oscillate_reset ;
                                  step = oscillate_step }
type ('b , 'a) _decrease =
  { mutable i_74 : 'b ; mutable m_71 : 'a }

let decrease  = 
  
  let decrease_alloc _ =
    ();{ i_74 = (false:bool) ; m_71 = (Obj.magic ():'b) } in
  let decrease_reset self  =
    (self.i_74 <- true:unit) in 
  let decrease_step self (x_70:'a667) =
    ((let (x_73:bool) = if self.i_74 then true else (<) x_70  self.m_71 in
      self.i_74 <- false ; self.m_71 <- x_70 ; x_73):bool) in
  Node { alloc = decrease_alloc; reset = decrease_reset ;
                                 step = decrease_step }
type ('b , 'a) _constant =
  { mutable i_79 : 'b ; mutable m_76 : 'a }

let constant  = 
  
  let constant_alloc _ =
    ();{ i_79 = (false:bool) ; m_76 = (Obj.magic ():'c) } in
  let constant_reset self  =
    (self.i_79 <- true:unit) in 
  let constant_step self (x_75:'a676) =
    ((let (x_78:bool) = if self.i_79 then true else (=) x_75  self.m_76 in
      self.i_79 <- false ; self.m_76 <- x_75 ; x_78):bool) in
  Node { alloc = constant_alloc; reset = constant_reset ;
                                 step = constant_step }
type ('b , 'a) _edge =
  { mutable i_84 : 'b ; mutable m_81 : 'a }

let edge  = 
   let edge_alloc _ =
     ();{ i_84 = (false:bool) ; m_81 = (false:bool) } in
  let edge_reset self  =
    (self.i_84 <- true:unit) in 
  let edge_step self (x_80:bool) =
    ((let (x_83:bool) =
          if self.i_84 then x_80 else (&&) x_80  (not self.m_81) in
      self.i_84 <- false ; self.m_81 <- x_80 ; x_83):bool) in
  Node { alloc = edge_alloc; reset = edge_reset ; step = edge_step }
