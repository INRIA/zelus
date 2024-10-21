## Build zrun, compiler and libraries
all: zrun.exe zwrite.exe zeluc.exe

zrun.exe:
	(cd src; dune build -- zrun.exe)

zwrite.exe:
	(cd src; dune build -- zwrite.exe)

zeluc.exe:
	(cd src; dune build -- zeluc.exe)

zrun.exe.verbose:
	(cd src; dune build --verbose -- zrun.exe)

tests:
	(cd tests; dune test)

debug:
	(cd src; dune build --debug-backtraces --debug-dependency-path -- zrun.bc)
	(cd src; dune build --debug-backtraces --debug-dependency-path -- zwrite.bc)
	(cd src; dune build --debug-backtraces --debug-dependency-path -- zeluc.bc)

clean:
	dune clean;
	(cd tests/good/; rm -f *.zlo);
	(cd tests/bad/; rm -f *.zlo)

wc:
	(cd src;
	wc global/*.ml \
	parsing/parsetree.ml parsing/*.mll \
	zrun/*.ml \
	tydefs/*.ml \
	compiler/rewrite/*.ml \
	compiler/typing/*.ml \
	compiler/analysis/*.ml \
	compiler/gencode/*.ml \
	compiler/main/*.ml)


# Extract the ZRun interpreter from the development
zrun.update.git:
	rm -r -f zrun.update.git;
	mkdir zrun.update.git;
	cp -r configure zrun.update.git;
	cp -r config.ml zrun.update.git;
	cp -r src/global zrun.update.git/src;
	cp -r src/parser zrun.update.git/src;
	cp -r zrun/zrun zrun.update.git/src;	

.PHONY: zeluc.exe zeluc.exe zrun.exe zwrite.exe zrun.exe.verbose tests debug clean wc
