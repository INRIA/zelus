all: zeluc.exe

## Build the compiler and libraries
## dune build src lib

zeluc.exe:
	(cd src; dune build -- zeluc.exe);
	dune build lib

tests:
	dune test

debug:
	(cd src; dune build --debug-backtraces --debug-dependency-path -- zeluc.bc)

opam-install: ## Install as an opam development package pinned to this directory
	opam pin -k path .

opam-uninstall: ## Remove opam pin
	opam pin remove zelus zelus-gtk

clean:
	dune clean;
	(cd tests/good/; rm -f *.zlo);
	(cd tests/bad/; rm -f *.zlo)

wc:
	(cd src; \
	wc global/*.ml \
	parsing/parsetree.ml parsing/*.mll \
	zrun/*.ml \
	compiler/common/*.ml \
	compiler/typdefs/*.ml \
	compiler/rewrite/*.ml \
	compiler/typing/*.ml \
	compiler/analysis/*.ml \
	compiler/gencode/*.ml \
	compiler/main/*.ml)

.PHONY: zeluc.exe zeluc.exe zrun.exe zwrite.exe zrun.exe.verbose tests debug clean wc

# Doc (for opam):
# opam pin -k path .              : install the current version of the compiler
#                                   as an opam package
# opam pin --help

# opam pin remove zelus zelus-gtk : removes the opam package
# opam install zelus zelus-gtk : install the (public) opam package

