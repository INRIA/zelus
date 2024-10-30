## Build the compiler and libraries
all: zeluc.exe

zeluc.exe:
	(cd src; dune build -- zeluc.exe)

tests:
	(cd tests; dune test)

debug:
	(cd src; dune build --debug-backtraces --debug-dependency-path -- zeluc.bc)

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
