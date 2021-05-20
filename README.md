[![Actions Status](https://github.com/INRIA/zelus/workflows/Build/badge.svg)](https://github.com/INRIA/zelus/actions)
[![Actions Status](https://github.com/INRIA/zelus/workflows/Opam/badge.svg)](https://github.com/INRIA/zelus/actions)

# Zelus: A Synchronous Language with ODEs

Zélus is a synchronous language extended with Ordinary Differential Equations (ODEs) to program hybrid systems that mix discrete-time and continuous-time models.
An example is a (discrete-time) model of a control software paired with a (continuous-time) model of the plant.
The language shares the basic principles of the synchronous languages [Lustre](https://www-verimag.imag.fr/DIST-TOOLS/SYNCHRONE/lustre-v6/) with modularity features from [Lucid Synchrone](http://www.di.ens.fr/~pouzet/lucid-synchrone/) (type inference, hierarchical automata, and higher-order functions).
It is conservatively extended to write continuous-time models expressed by ODEs and zero-crossing events.
The compiler is written in [OCaml](https://ocaml.org/) and is structured as a series of source-to-source and traceable transformations that ultimately yield statically scheduled sequential code.
Continuous-time models are simulated using an off-the-shelf numerical solver (here [Sundials CVODE](https://computation.llnl.gov/casc/sundials/description/description.html#descr_cvode) and, for the moment, the two built-in solvers ode23 and ode45).

## Getting Started

The easiest way to install Zelus is via [Opam](https://opam.ocaml.org/), the OCaml package manager.

```
opam install zelus
```

You can then test your installation with:
```
zeluc -version
```

The manual, examples, and research papers can be found at http://zelus.di.ens.fr

### Optional Dependencies

By default Zelus relies on the built-in solvers.
To switch to Sundials CVODE you need to install sundialsml (which requires sundials).
Some examples also depend on the zelus gtk library (which requires gtk2.0)

```
opam install sundialsml zelus-gtk
```

### Docker

We also provide a dockerfile to setup an environment with all the dependencies.
Build the image with (you might need to increase available memory in docker preferences):
```
make docker-build
```

Run with:
```
make docker-run
```


##  A Simple Example

Consider the example of a bouncing ball.
The zelus code is the following:

```ocaml
let loose = 0.8
let     g = 9.81
let    x0 = 0.0 
let    y0 = 10.0
let   x'0 = 1.0
let   y'0 = 0.0

let hybrid main () = () where
  rec der x  =  x' init x0
  and der y  =  y' init y0
  and der x' = 0.0 init x'0
  and der y' = -.g init y'0 reset up(-.y) -> -.loose *. last y'
  and present up(-.y) -> local cpt in
    do  cpt = 0 fby cpt + 1
    and  () = print_endline (string_of_int cpt) done
```

The dynamics of the ball is expressed with four ODEs defining the position `(x, y)` and the speed `(x', y')` of the ball given an initial position `(x0, y0)` and an initial speed `(x'0, y'0)`.
Whenever the ball hits the ground `up(-. y)` the discrete time code of the body of the `present` construct is executed (here incrementing a simple counter).

### Compilation
The zeluc compiler takes a zelus file (e.g., `bouncing.zls`) and compile it to OCaml code (e.g., `bouncing.ml`).

```
zeluc bouncing.zls
```

You can also specify a simulation node.
The compiler then generates an additional file containing the simulation code (e.g., `main.ml`).

```
zeluc -s main bouncing.zls
```

To build an executable, the last thing to do is to compile the OCaml code using the `zelus` library.

```
ocamlfind ocamlc -linkpkg -package zelus bouncing.ml main.ml -o bouncing
```

## Other Examples

This repository includes runnable examples demonstrating different aspects of the language. 
The source code for several of the examples can be found in the `examples` directory.
To build most of the examples:

```
cd examples && make
```

The executables can be found in each example directory (e.g., `horloge/horloge_main.exe`).

## Development

### Compiler

We use [dune](https://dune.readthedocs.io/en/stable/) to build the compiler, the libraries, and the examples.
To build the project:

```
./configure
dune build
```

This produces two executables (and some tools in `./tools`):
- `compiler/zeluc.exe`: native code
- `compiler/zeluc.bc`: byte code (can be used with ocamldebug)

Libraries are split in two packages:
- `zelus`: the standard libraries
- `zelus-gtk`: additional libraries that depend on lablgtk (only built if lablgtk is installed)

The build automatically detects if sundialsml is installed and updates the librairies accordingly.

### Test

To run all the tests:
```
cd test
make
```

Tests are split into 3 categories: `good`, `bad`, and `run`.
To launch a single subset (e.g., `good`):
```
cd good
make
```

To clean generated files:
```
make clean
```

## Citing Zelus

```
@inproceedings{Zelus2013HSCC,
  author = {Timothy Bourke and Marc Pouzet},
  title = {Zélus: A Synchronous Language with {ODEs}},
  booktitle = {16th International Conference on Hybrid Systems: Computation and Control (HSCC'13)},
  pages = {113--118},
  month = mar,
  year = 2013,
}
```
