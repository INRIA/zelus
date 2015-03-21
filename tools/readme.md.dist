# Zélus #

This distribution includes the byte code of the Zélus compiler and the
source code of several examples written in the Zélus language.

Zélus is developed by Marc Pouzet and Timothy Bourke in the Inria/ENS team
PARKAS.

Please contact us by email if you have any problems or questions:
<Timothy.Bourke@inria.fr>, <Marc.Pouzet@ens.fr>.

## Installation and examples ##

This software requires OCaml (v4.02.1):
  <http://caml.inria.fr/ocaml/>

Most of the examples also require lablgtk2 (2.18.3):
  <http://lablgtk.forge.ocamlcore.org/>

The 'sundials' distribution also requires Sundials/ML (2.5.x):
  <http://inria-parkas.github.io/sundialsml/>

These dependencies are available through opam:

    opam install ocamlfind lablgtk sundialsml

Basic instructions:

    ./configure
    make examples

More details and descriptions of the examples are available online:
    http://www.di.ens.fr/~pouzet/zelus

## Compiling programs ##

Programs are compiled in two steps.

1.  Compile Zélus (.zls) code into OCaml (.ml).

        zeluc -s main -gtk2 bangbang.ml

    The `-s` option generates a simulation stub for the given node (here
    `main`) in an OCaml file with the same name (here `main.ml`).

    The `-gtk2` option is needed for programs that use lablgtk2. Without
    this option programs crash at runtime with the message:
        Fatal error: exception Gpointer.Null

2.  Compile the OCaml code into an executable.

    The simplest solution is to use `ocamlfind`:

        ocamlfind ocamlc -o bangbang -package zelus.gtk -linkpkg bangbang.ml main.ml

    Otherwise all dependencies must be specified in the correct order:

        ocamlc -o bangbang              \
            -I `zeluc -where`           \
            -I +sundialsml              \
            -I +lablgtk2                \
            unix.cma bigarray.cma       \
            sundials.cma lablgtk.cma    \
            zllibgtk.cma                \
            bangbang.ml main.ml

    Or without lablgtk2:

        ocamlc -o bangbang              \
            -I `zeluc -where`           \
            -I +sundialsml              \
            unix.cma bigarray.cma       \
            sundials.cma                \
            zllib.cma                   \
            file.ml node.ml

