all:
	dune build 

debug:
	dune build --debug-backtraces --debug-dependency-path

clean:
	dune clean; rm -f *~; (cd zrun/tests; make clean)

wc:
	wc compiler/global/*.ml \
	compiler/typing/*.ml \
	compiler/main/*.ml \
	compiler/parsing/*.mll compiler/parsing/*.mly \
	zrun/*.ml
