include ../../../config

ZELUC = ../../../bin/zeluc
ZLLIB = ../../../lib

ZELUCFLAGS += -nodeadcode
ZLEXTRALIBS=$(ZLGTKLIBS)

THETA=3
PWTRNFLAGS=-dt
SAMPLING=0.1

all: byte

byte: main

main: mainc.byte maind.byte

model.ml: zlarray.zci fixed_step_solvers.zci powertrain.zci model.zls
	$(ZELUC) $(ZELUCFLAGS) model.zls

main%.ml: zlarray.zci fixed_step_solvers.zci powertrain.zci model.zls
	$(ZELUC) $(ZELUCFLAGS) -gtk2 -s $(@:.ml=) model.zls

mainc.byte: zlarray.cmo fixed_step_solvers.cmo powertrain.cmo model.ml mainc.ml
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) \
			zlarray.cmo fixed_step_solvers.cmo powertrain.ml model.ml mainc.ml

maind.byte: zlarray.cmo fixed_step_solvers.cmo powertrain.cmo model.ml maind.ml
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) \
			zlarray.cmo fixed_step_solvers.cmo powertrain.ml model.ml maind.ml

simple_main: simple_powertrain.byte

simple_powertrain.ml:
	$(ZELUC) $(ZELUCFLAGS) -gtk2 -s main -o simple_powertrain_main simple_powertrain.zls

%.ml: %.zls
	$(ZELUC) $(ZELUCFLAGS) $<

fixed_step_solvers.ml: zlarray.zci
powertrain.ml: zlarray.zci

powertrain.zls:
	./gen_pwtrn $(PWTRNFLAGS) $(THETA)

clean:
	-@rm -f mainc.ml maind.ml mainc_main.ml maind_main.ml
	-@rm -f powertrain.ml
	-@rm -f model.ml main.ml mainc.ml
	-@rm -f simple_powertrain.ml simple_powertrain_main.ml
	-@rm -f fixed_step_solvers.ml
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci

realclean cleanall: clean
	-@rm -f mainc.byte maind.byte mainc.byte maind.byte
	-@rm -f simple_powertrain.byte
	-@rm -f powertrain.zls powertrain.zli
