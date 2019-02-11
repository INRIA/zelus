include ../../config

.PHONY: test debug

OCAMLFLAGS += -I ../../lib
ZLEXTRALIBS = $(ZLGTKLIBS)

default: $(word 1, $(targets))
all:  $(targets)
byte: autotransc.byte autotrans_gui.byte autotransd.byte
opt:
	@echo $(S_RED)TODO:$(S_NORMAL) implement rule opt

# ------------------------------------

autotrans_gui.byte: ZLEXTRALIBS = $(ZLGTKLIBS)
autotrans_gui.byte: ZELUCFLAGS += -gtk2
autotrans_gui.byte: maneuvers.cmo utils.cmo consts.cmo draw.cmo common.cmo \
    		 autotransc.cmo autotrans_gui.cmo autotrans_gui_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ \
	    $(ZLSTDLIBS) $(ZLEXTRALIBS) graphics.cma \
			$(INCLUDES) $^

autotrans_gui.ml autotrans_gui_main.ml: autotrans_gui.zls \
				 autotransc.zci draw.zci common.zci
	$(ZELUC) $(ZELUCFLAGS) $(ZELUCEXTRAFLAGS) -s main $<
	mv main.ml autotrans_gui_main.ml

autotrans_gui.cmo: common.cmo
autotrans_gui_main.cmo: autotrans_gui.cmo

autotrans_gui.cmi autotrans_gui.cmo: INCLUDES += $(LABLGTK2)
autotrans_gui.cmo: autotrans_gui.ml autotransc.cmi draw.cmi common.cmi

# ------------------------------------

autotransc.byte: ZLEXTRALIBS = $(ZLGTKLIBS)
autotransc.byte: ZELUCFLAGS += -gtk2
autotransc.byte: maneuvers.cmo utils.cmo consts.cmo common.cmo \
    		 autotransc.cmo autotransc_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ \
	   $(ZLSTDLIBS) $(ZLEXTRALIBS) \
		 $(INCLUDES) $^

autotransc.ml autotransc_main.ml: autotransc.zls common.zci
	$(ZELUC) $(ZELUCFLAGS) $(ZELUCEXTRAFLAGS) -s main $<
	mv main.ml autotransc_main.ml

autotransc.cmo: common.cmo
autotransc_main.cmo: autotransc.cmo

autotransc.cmi autotransc.cmo:
autotransc.cmo: autotransc.ml common.cmi

# ------------------------------------

autotransd.byte: ZLEXTRALIBS = $(ZLGTKLIBS)
autotransd.byte: ZELUCFLAGS += -gtk2
autotransd.byte: maneuvers.cmo utils.cmo consts.cmo common.cmo \
    		 autotransd.cmo autotransd_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ \
	    $(ZLSTDLIBS) $(ZLEXTRALIBS) \
			$(INCLUDES) $^

autotransd.ml autotransd_main.ml: autotransd.zls common.zci
	$(ZELUC) $(ZELUCFLAGS) $(ZELUCEXTRAFLAGS) -s main $<
	mv main.ml autotransd_main.ml

autotransd.cmo: common.cmo
autotransd_main.cmo: autotransd.cmo

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

%.zci %.ml: %.zls
	$(ZELUC) $(ZELUCFLAGS) $<

# ------------------------------------

export:
	mkdir $(DISTDIR)/autotrans
	cp consts.ml consts.zli draw.ml draw.zli utils.ml utils.zli common.zls\
		 autotrans.zls autotransd.zls Makefile $(DISTDIR)/autotrans/

clean:
	-@rm -f autotransc_main.ml autotransc.ml
	-@rm -f autotrans_gui_main.ml autotrans_gui.ml
	-@rm -f autotransd_main.ml autotransd.ml
	-@rm -f common.ml
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci

cleanall: clean
	-@rm -f autotransc.byte autotransc.opt
	-@rm -f autotrans_gui.byte autotrans_gui.opt
	-@rm -f autotransd.byte autotransd.opt
