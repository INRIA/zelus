include ../../config

.PHONY: test debug

ZLEXTRALIBS = $(ZLGTKLIBS)

default: $(word 1, $(targets))
all:  $(targets)
byte: autotransc.byte autotrans_gui.byte autotransd.byte

# ------------------------------------

autotrans_gui.byte: INCLUDES += $(LABLGTK2) $(SUNDIALS)
autotrans_gui.byte: ZELUCFLAGS += -gtk2 -nodeadcode
autotrans_gui.byte: utils.cmo consts.cmo draw.cmo common.cmo \
    		 autotransc.cmo autotrans_gui.cmo autotrans_gui_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) graphics.cma $(ZLGTKLIBS) $^

autotrans_gui.ml autotrans_gui_main.ml: autotrans_gui.zls \
				 autotransc.zci draw.zci common.zci
	$(ZELUC) $(ZELUCFLAGS) $(ZELUCEXTRAFLAGS) -s main $<
	mv main.ml autotrans_gui_main.ml

autotrans_gui.cmi autotrans_gui.cmo: INCLUDES += $(LABLGTK2)
autotrans_gui.cmo: autotrans_gui.ml autotransc.cmi draw.cmi common.cmi

# ------------------------------------

autotransc.byte: INCLUDES += $(LABLGTK2) $(SUNDIALS)
autotransc.byte: ZELUCFLAGS += -gtk2
autotransc.byte: utils.cmo consts.cmo common.cmo \
    		 autotransc.cmo autotransc.cmo autotransc_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) $(ZLGTKLIBS) $^

autotransc.ml autotransc_main.ml: autotransc.zls common.zci
	$(ZELUC) $(ZELUCFLAGS) $(ZELUCEXTRAFLAGS) -s main $<
	mv main.ml autotransc_main.ml

autotransc.cmi autotransc.cmo: INCLUDES += $(LABLGTK2)
autotransc.cmo: autotransc.ml common.cmi

# ------------------------------------

autotransd.byte: INCLUDES += $(LABLGTK2) $(SUNDIALS)
autotransd.byte: ZELUCFLAGS += -gtk2
autotransd.byte: utils.cmo consts.cmo common.cmo \
    		 autotransd.cmo autotransd_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) $(ZLGTKLIBS) $^

autotransd.ml autotransd_main.ml: autotransd.zls common.zci
	$(ZELUC) $(ZELUCFLAGS) $(ZELUCEXTRAFLAGS) -s main $<
	mv main.ml autotransd_main.ml

autotransd.cmi autotransd.cmo: INCLUDES += $(LABLGTK2)
autotransd.cmo: autotransd.ml common.cmi

# ------------------------------------

common.ml: common.zls consts.zci utils.zci
	$(ZELUC) $(ZELUCFLAGS) $<
common.cmo common.cmi common.zci: common.ml consts.cmi utils.cmi

# ------------------------------------

consts.cmo consts.cmi: consts.ml
draw.cmo draw.cmi: draw.ml
utils.cmo utils.cmi: utils.ml

# ------------------------------------

export:
	mkdir $(DISTDIR)/autotrans
	cp consts.ml consts.zli draw.ml draw.zli utils.ml utils.zli common.zls\
		 autotrans.zls autotransd.zls Makefile $(DISTDIR)/autotrans/

clean realclean cleanall:
	-@rm -f autotransc_main.ml autotransc.ml
	-@rm -f autotrans_gui_main.ml autotrans_gui.ml
	-@rm -f autotransd_main.ml autotransd.ml
	-@rm -f common.ml
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci
	-@rm -f autotransc.byte autotransc.opt
	-@rm -f autotrans_gui.byte autotrans_gui.opt
	-@rm -f autotransd.byte autotransd.opt
