# Zelus: A Synchronous Language with ODEs

Zélus is a synchronous language extended with Ordinary Differential Equations (ODEs) to program hybrid systems that mix discrete-time and continuous-time models. 
An example is a (discrete-time) model of a control software paired with a (continuous-time) model of the plant. 
The language shares the basic principles of the synchronous languages [Lustre](http://www-verimag.imag.fr/Synchrone,30?lang=en) with modularity features from [Lucid Synchrone](http://www.di.ens.fr/~pouzet/lucid-synchrone/) (type inference, hierarchical automata, and higher-order functions).
It is conservatively extended to write continuous-time models expressed by ODEs and zero-crossing events.
The compiler is written in [OCaml](http://caml.inria.fr/ocaml/) and is structured as a series of source-to-source and traceable transformations that ultimately yield statically scheduled sequential code.
Continuous-time models are simulated using an off-the-shelf numerical solver (here [Sundials CVODE](https://computation.llnl.gov/casc/sundials/description/description.html#descr_cvode) and, for the moment, the two built-in solvers ode23 and ode45).

## Getting Started

The easiest way to install Zelus is via [Opam](https://opam.ocaml.org/), the OCaml package manager.

```
opam install .
```

You can then test your installation with:
```
zeluc -version
```

The manual, examples, and research papers can be found at http://zelus.di.ens.fr

### Optional Dependencies

By default Zelus relies on the built-in solvers.
To switch to Sundials CVODE you need to install sundialsml (which requires sundials).
Some examples also depend on lablgtk (which requires gtk2.0)

```
opam install sundialsml lablgtk
```

You can then reinstall zelus

```
opam reinstall zelus
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


##  Examples

This repository includes runnable examples demonstrating different aspects of the language. 
The source code for several of the examples can be found in the `examples` directory.
To build most of the examples:

```
cd examples && make
```

The excutables can be found in each example directory (e.g., `horloge/horloge_main.exe`).


## Development

### Compiler

We use [dune](https://dune.readthedocs.io/en/stable/) to build the compiler, the libraries, and the examples.
To build the project:

```
dune build
```

This produces two executables:
- `compiler/zeluc.exe`: the compiler
- `compiler/zlsdep.exe`: a tool to track dependencies between zelus files

Libraries are split in two packages:
- `zelus`: the standard libraries
- `zelus-gtk`: additional libraries that depend on lablgtk (only built if lablgtk is installed)

The build automatically detects if sundialsml is installed and update the librairies accordingly.


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