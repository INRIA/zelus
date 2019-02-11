include ../../config

.PHONY: test debug

ZLEXTRALIBS = $(ZLGTKLIBS)

default: $(word 1, $(targets))
all:  $(targets)
byte: airtraffic.byte
opt:  airtraffic.opt

airtraffic.byte: INCLUDES += $(LABLGTK2) $(SUNDIALS)
airtraffic.byte: simplevector.cmo a330.cmo airtrafficgui.cmo \
    		 airtraffic.cmo airtraffic_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) $(ZLGTKLIBS) $^

airtraffic.opt: INCLUDES += $(LABLGTK2) $(SUNDIALS)
airtraffic.opt: simplevector.cmx a330.cmx airtrafficgui.cmx \
    		 airtraffic.cmx airtraffic_main.cmx
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) $(ZLGTKLIBS:.cma=.cmxa) $^

airtraffic.zls: airtrafficgui.zci

airtrafficgui.cmi airtrafficgui.cmo airtrafficgui.cmx: INCLUDES += $(LABLGTK2)
airtrafficgui.cmi: airtrafficgui.mli
airtrafficgui.cmo airtrafficgui.cmx: airtrafficgui.ml airtrafficgui.cmi simplevector.cmi a330.cmi

a330.cmx a330.cmo a330.cmi: a330.ml simplevector.cmi

#a330.ml: a330-simple.svg
#	./svgtoocaml.py $< > $@

airtrafficgui.zci: airtrafficgui.zli

airtraffic.cmi airtraffic.cmo airtraffic.cmx: airtraffic.ml

test: airtrafficgui.cmi a330.ml
	@cp airtrafficgui.ml airtrafficgui_test.ml
	@printf "let _ = runtest () ;;\n" >> airtrafficgui_test.ml
	$(OCAMLC) -o test $(LABLGTK2) lablgtk.cma gtkInit.cmo \
	    simplevector.ml a330.ml airtrafficgui_test.ml

debug: airtraffic.zls airtrafficgui.zci
	$(ZELUC) -v $(ZELUCFLAGS) -gtk2 -s main $< \
	    2>&1

airtraffic.ml airtraffic_main.ml: airtraffic.zls airtrafficgui.zci
	$(ZELUC) $(ZELUCFLAGS) -gtk2 -s main $<
	mv main.ml airtraffic_main.ml

# version rotation

airtrafficrot.byte: INCLUDES += $(LABLGTK2) $(SUNDIALS)
airtrafficrot.byte: simplevector.cmo a330.cmo airtrafficgui.cmo \
		    airtrafficrot.cmo airtrafficrot_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) $(ZLGTKLIBS) $^

airtrafficrot.opt: INCLUDES += $(LABLGTK2) $(SUNDIALS)
airtrafficrot.opt: simplevector.cmx a330.cmx airtrafficgui.cmx \
		    airtrafficrot.cmx airtrafficrot_main.cmx
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) $(ZLGTKLIBS:.cma=.cmxa) $^

airtrafficrot.ml airtrafficrot_main.ml: airtrafficrot.zls airtrafficgui.zci
	$(ZELUC) $(ZELUCFLAGS) -gtk2 -s main $<
	mv main.ml airtrafficrot_main.ml

#

# version tpb

airtraffictpb.byte: INCLUDES += -I $(LABLGTK2) $(SUNDIALS)
airtraffictpb.byte: simplevector.cmo a330.cmo airtrafficgui.cmo \
		    airtraffictpb.cmo airtraffictpb_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) $(ZLGTKLIBS) $^

airtraffictpb.opt: INCLUDES += -I $(LABLGTK2) $(SUNDIALS)
airtraffictpb.opt: simplevector.cmx a330.cmx airtrafficgui.cmx \
		    airtraffictpb.cmx airtraffictpb_main.cmx
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) $(ZLGTKLIBS:.cma=.cmxa) $^

airtraffictpb.ml airtraffictpb_main.ml: airtraffictpb.zls airtrafficgui.zci
	$(ZELUC) $(ZELUCFLAGS) -gtk2 -s main $<
	mv main.ml airtraffictpb_main.ml

#

export:
	mkdir $(DISTDIR)/airtraffic
	cp a330.ml airtrafficgui.zli airtrafficgui.ml airtrafficgui.mli \
	   simplevector.ml airtraffic.zls Makefile readme.md \
	   $(DISTDIR)/airtraffic/
	mkdir $(DISTDIR)/airtraffic/img
	cp img/*.png $(DISTDIR)/airtraffic/img/
	make -C slides
	cp slides/slides.pdf $(DISTDIR)/airtraffic/

clean realclean cleanall:
	-@rm -f airtraffic_main.ml airtraffic.ml
	-@rm -f airtrafficgui_test.ml
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci
	-@rm -f airtraffic.byte airtraffic.opt test
	-@if [ -d slides ]; then make -s -C slides clean; fi
