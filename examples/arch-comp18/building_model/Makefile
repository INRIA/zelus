include ../../../config

ZELUC = ../../../bin/zeluc
ZLLIB = ../../../lib

ZLEXTRALIBS=$(ZLGTKLIBS)

NODES = build6_bldc01 build15_bldc01 build25_bldc01 build48_bldc01

all: byte

byte: models.cmo $(NODES:=.byte)
opt: models.cmx $(NODES:=.opt)

%.byte: %.ml
	$(OCAMLC) $(OCAMLFLAGS) -o $@ \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) \
			$(INCLUDES) $<

%.opt: %.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ \
	    -I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) \
			$(INCLUDES:.cmo=.cmx) $<

build%.ml:
	$(ZELUC) $(ZELUCFLAGS) -gtk2 -s $(@:.ml=) main.zls

%.ml: %.zls
	$(ZELUC) $(ZELUCFLAGS) $<

main.ml: models.ml main.zls
build6_bldc01.byte: INCLUDES += models.cmo main.cmo
build6_bldc01.byte: models.cmo main.cmo
build15_bldc01.byte: INCLUDES += models.cmo main.cmo
build15_bldc01.byte: models.cmo main.cmo
build25_bldc01.byte: INCLUDES += models.cmo main.cmo
build25_bldc01.byte: models.cmo main.cmo
build48_bldc01.byte: INCLUDES += models.cmo main.cmo
build48_bldc01.byte: models.cmo main.cmo
build6_bldc01.opt: INCLUDES += models.cmx main.cmx
build6_bldc01.opt: models.cmx main.cmx
build15_bldc01.opt: INCLUDES += models.cmx main.cmx
build15_bldc01.opt: models.cmx main.cmx
build25_bldc01.opt: INCLUDES += models.cmx main.cmx
build25_bldc01.opt: models.cmx main.cmx
build48_bldc01.opt: INCLUDES += models.cmx main.cmx
build48_bldc01.opt: models.cmx main.cmx

clean:
	-@rm -f models.zci models.ml main.zci main.ml
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci

realclean cleanall: clean
	-@rm -f *.opt *.byte
