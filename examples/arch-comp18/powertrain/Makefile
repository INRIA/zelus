include ../../../config

ZELUC = ../../../bin/zeluc
ZLLIB = ../../../lib

ZELUCFLAGS += -nodeadcode
ZLEXTRALIBS=$(ZLGTKLIBS)

THETA=1
SAMPLING=0.1

all: byte

byte: main

main: mainc.byte maind.byte

main.ml: zlarray.zci disc_solvers.zci powertrain.zci main.zls
	$(ZELUC) $(ZELUCFLAGS) main.zls

main%.ml: zlarray.zci disc_solvers.zci powertrain.zci main.zls
	$(ZELUC) $(ZELUCFLAGS) -gtk2 -s $(@:.ml=) main.zls

mainc.byte: zlarray.cmo disc_solvers.cmo powertrain.cmo main.ml mainc.ml
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) \
			zlarray.cmo disc_solvers.cmo powertrain.ml main.ml mainc.ml

maind.byte: zlarray.cmo disc_solvers.cmo powertrain.cmo main.ml maind.ml
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) \
			zlarray.cmo disc_solvers.cmo powertrain.ml main.ml maind.ml

spaceex_main: spaceex_powertrain.byte

spaceex_powertrain.ml:
	$(ZELUC) $(ZELUCFLAGS) -gtk2 -s main -o spaceex_powertrain_main spaceex_powertrain.zls

%.ml: %.zls
	$(ZELUC) $(ZELUCFLAGS) $<

disc_solvers.ml: zlarray.zci
powertrain.ml: zlarray.zci

powertrain.zls:
	./gen_pwtrn $(THETA)

clean:
	-@rm -f main.ml mainc.ml maind.ml mainc_main.ml maind_main.ml
	-@rm -f spaceex_powertrain.ml spaceex_powertrain_main.ml
	-@rm -f powertrain.ml disc_solvers.ml
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci

realclean cleanall: clean
	-@rm -f mainc.byte maind.byte mainc.byte maind.byte
	-@rm -f simple_powertrain.byte
	-@rm -f powertrain.zls powertrain.zli
