include ../../config

.PHONY: test debug

ZLEXTRALIBS = $(ZLGTKLIBS)

default: $(word 1, $(targets))
all:  $(targets)
byte: autotrans.byte
opt:  autotrans.opt

autotrans.byte: INCLUDES += $(LABLGTK2) $(SUNDIALS)
autotrans.byte: consts.cmo draw.cmo utils.cmo \
    		 autotrans.cmo autotrans_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) graphics.cma $(ZLGTKLIBS) $^

autotrans.cmi autotrans.cmo: INCLUDES += $(LABLGTK2)
autotrans.cmo: autotrans.ml autotrans.cmi consts.cmi draw.cmi utils.cmi

consts.cmo consts.cmi: consts.ml

draw.cmo draw.cmi: INCLUDES +=
draw.cmo draw.cmi: draw.ml

utils.cmo utils.cmi: utils.ml

autotrans.ml autotrans_main.ml: autotrans.zls draw.zci consts.zci utils.zci
	$(ZELUC) $(ZELUCFLAGS) -gtk2 -nodeadcode -s main $<
	mv main.ml autotrans_main.ml

export:
	mkdir $(DISTDIR)/autotrans
	cp consts.ml consts.zli draw.ml draw.zli utils.ml utils.zli \
		 autotrans.zls Makefile $(DISTDIR)/autotrans/

clean realclean cleanall:
	-@rm -f autotrans_main.ml autotrans.ml
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci
	-@rm -f autotrans.byte autotrans.opt
