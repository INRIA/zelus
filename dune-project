(lang dune 2.6)
(using menhir 2.0)

(name zelus)

(package 
 (name zelus)
 (depends
  (dune (> 2.6))
  ocamlfind
  menhir
  graphics))


(package 
 (name zelus-gtk)
 (depends
  zelus
  lablgtk))
