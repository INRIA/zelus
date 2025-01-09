all:
	dune test

# dune build -- zeluctest.exe
#debug:
#	dune build --debug-backtraces --debug-dependency-path -- zeluctest.bc

clean:
	dune clean
	(cd good; rm -r -f *.zci *~)
	(cd bad; rm -r -f *.zci *~)

