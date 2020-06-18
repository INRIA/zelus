# Installation

You can either install zelus from sources or with docker

## From sources

- Requirements
  - Mandatory:
    - Ocaml (>= 4.10.0)
    - Menhir
  - Optional:
    - SundialsML
    - Lablgtk2
    - glMLite

Installing requirements on a fresh ubuntu 18.10 machine (with opam):

```
# system requirements
sudo apt-get update
sudo apt-get upgrade -y
sudo apt-get install -y build-essential sudo m4 libgtk2.0-dev libsundials-dev curl

# install opam
sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)

source ~/.bashrc

# ocaml requirements
opam init -a
opam switch 4.08.0
eval $(opam env)
opam update
opam upgrade -y
eval $(opam env)
opam install -y ocamlfind menhir sundialsml lablgtk
evam $(opam env)

# installation
./configure
make
make install
```

## Docker container

```
make docker_build
make docker_run
```

----------------------------------------------------------------------

# Development

Debugging the compiler:

1. Build the compiler with debugging symbols:
      make clean debug

2. Start emacs, then
      M-x camldebug
      Run camldebug on file: compiler/zeluc.byte
      Caml debugger to run:  ocamldebug

3. In the Ocaml debugger, copy-and-paste the commands listed in debug.txt,
   changing the last to include any additional flags and the path to the
   file to compile (relative to the compiler/ subdirectory).

4. Debug! (e.g.: run, step, break, etc.)


Profiling generated executables:

1. Compile the library using ocamlcp:
      cd lib; make clean OCAMLC="ocamlcp -p a" byte

2. Compile the output of zeluc using ocamlcp, e.g.,
      cd examples/bouncingball; make clean OCAMLC="ocamlcp -p a" byte

3. Run the program (using -maxt to terminate normally):
      rm -f ocamlprof.dump # do not accumulate
      ./ball.byte -sundialsI -maxt 15

4. Examine the files:
      ocamlprof ball.ml
      ocamlprof ball_main.ml
      ocamlprof ../../lib/zlsolve.ml
      ocamlprof ../../lib/solvers.ml
      ocamlprof ../../lib/solvers/solversundials.ml
      ocamlprof ../../lib/solvers/illinois.ml


Time profiling generated executables:

1. Compile the library with ocamlopt -p:
      cd lib; make clean OCAMLOPTFLAGS=-p opt

2. Compile the output of zeluc using ocamlopt -p, e.g.,
      cd examples/bouncingball; make clean OCAMLOPTFLAGS=-p ball.opt

3. Run the program and examine the results:
      ./ball.opt -sundialsI -maxt 15
      gprof ball.opt
