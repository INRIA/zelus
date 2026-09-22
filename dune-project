(lang dune 3.21)
;(using menhir 2.1)
(map_workspace_root false)

; the debugger does not work with dune 3.0 and above. Why?
; (lang dune 3.21)
(using menhir 3.0)


; Disabled for now due to ./configure script
; (generate_opam_files)

; Is (wrapped_executables false) useful?
; not clear; it works also if removed;
(wrapped_executables false)

(source
 (github INRIA/zelus))

(license "INRIA Non-Commercial License Agreement")

(authors
 "Timothy Bourke <timothy.bourke@inria.fr>"
 "Marc Pouzet <marc.pouzet@ens.fr>")

(maintainers "Marc Pouzet <marc.pouzet@ens.fr>")

(package
 (name zelus)
 (version 3.0)
 (synopsis "A synchronous language with ODEs")
 (homepage "http://zelus.di.ens.fr")
 (documentation "http://zelus.di.ens.fr/man/")
 (bug_reports "https://github.com/INRIA/zelus/issues")
 (depends
  (ocaml
   (>= 5.3.0))
  menhir
  (alcotest :with-test)
  ppx_deriving))

(package
 (name zelus-gtk)
 (version 2.2)
 (synopsis "Zelus GTK library")
 (homepage "http://zelus.di.ens.fr")
 (documentation "http://zelus.di.ens.fr/man/")
 (bug_reports "https://github.com/INRIA/zelus/issues")
 (depends
  (ocaml
   (>= 5.3.0))
  zelus
  lablgtk))
