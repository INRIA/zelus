all:
	dune build -- zeluc.exe


debug:
	dune build --debug-backtraces --debug-dependency-path -- zeluc.bc

clean:
	dune clean
#; rm -f *~; (cd zrun/tests; make clean)

ML=global/*.ml \
   parsing/*.ml parsing/*.mll parsing/*.mly \
   typing/*.ml \
   analysis/*.ml \
   rewrite/*.ml \
   gencode/*.ml \
   main/*.ml

wc: ${ML}
	wc ${ML}

