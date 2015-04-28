include ../config

all: diff_log zltohtml

byte: all
opt: all
depend:

zltohtml: zltohtml.ml
	$(OCAMLC) -o $@ -I ../compiler/parsing lexer.cmo $^

zltohtml.ml: zltohtml.mll

diff_log: diff_log.ml
	$(OCAMLC) -o $@ str.cma $^

clean:
	rm -f *.annot *.cm[iox] *.o
	rm -f zltohtml.ml zltohtml

cleanall: clean
	rm -f zltohtml diff_log

