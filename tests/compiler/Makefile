all:
	dune test

# dune build -- zeluctest.exe
#debug:
#	dune build --debug-backtraces --debug-dependency-path -- zeluctest.bc

clean:
#	dune clean
	(cd good; rm -r -f *.zci *.zlo *~ *.out \
	*.ml *.cmi *.cmo *.cmxi *.cmxo *.o *.cmx)
	(cd bad; rm -r -f *.zci *.zlo *~ *.out \
	*.ml *.cmi *.cmo *.cmxi *.cmxo *.o *.cmx)

