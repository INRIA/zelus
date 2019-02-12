include ../../config

.PHONY: test debug

OCAMLFLAGS += -I ../../lib
OCAMLOPTFLAGS += -I ../../lib
ZLEXTRALIBS = $(ZLGTKLIBS)

default: $(word 1, $(targets))
all:  $(targets)
byte: autotransc.byte autotrans_gui.byte autotransd.byte
opt: autotransc.opt autotrans_gui.opt autotransd.opt

# ------------------------------------

autotrans_gui.byte: ZLEXTRALIBS = $(ZLGTKLIBS)
autotrans_gui.byte: ZELUCFLAGS += -gtk2
autotrans_gui.byte: maneuvers.cmo utils.cmo consts.cmo draw.cmo common.cmo \
    		 autotransc.cmo autotrans_gui.cmo autotrans_gui_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ \
	    $(ZLSTDLIBS) $(ZLEXTRALIBS) graphics.cma \
			$(INCLUDES) $^

autotrans_gui.opt: ZLEXTRALIBS = $(ZLGTKLIBS)
autotrans_gui.opt: ZELUCFLAGS += -gtk2
autotrans_gui.opt: maneuvers.cmx utils.cmx consts.cmx draw.cmx common.cmx \
    		 autotransc.cmx autotrans_gui.cmx autotrans_gui_main.cmx
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ \
	    $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) graphics.cmxa \
			$(INCLUDES:.cma=.cmxa) $^

autotrans_gui.ml autotrans_gui_main.ml: autotrans_gui.zls \
				 autotransc.zci draw.zci common.zci
	$(ZELUC) $(ZELUCFLAGS) $(ZELUCEXTRAFLAGS) -s main $<
	mv main.ml autotrans_gui_main.ml

autotrans_gui.cmo: common.cmo
autotrans_gui_main.cmo: autotrans_gui.cmo

autotrans_gui.cmx: common.cmx
autotrans_gui_main.cmx: autotrans_gui.cmx

autotrans_gui.cmi autotrans_gui.cmo autotrans_gui.cmx: INCLUDES += $(LABLGTK2)
autotrans_gui.cmo autotrans_gui.cmx: autotrans_gui.ml autotransc.cmi draw.cmi common.cmi

# ------------------------------------

autotransc.byte: ZLEXTRALIBS = $(ZLGTKLIBS)
autotransc.byte: ZELUCFLAGS += -gtk2
autotransc.byte: maneuvers.cmo utils.cmo consts.cmo common.cmo \
    		 autotransc.cmo autotransc_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ \
	   $(ZLSTDLIBS) $(ZLEXTRALIBS) \
		 $(INCLUDES) $^

autotransc.opt: ZLEXTRALIBS = $(ZLGTKLIBS)
autotransc.opt: ZELUCFLAGS += -gtk2
autotransc.opt: maneuvers.cmx utils.cmx consts.cmx common.cmx \
    		 autotransc.cmx autotransc_main.cmx
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ \
	   $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) \
		 $(INCLUDES:.cma=.cmxa) $^

autotransc.ml autotransc_main.ml: autotransc.zls common.zci
	$(ZELUC) $(ZELUCFLAGS) $(ZELUCEXTRAFLAGS) -s main $<
	mv main.ml autotransc_main.ml

autotransc.cmo: common.cmo
autotransc_main.cmo: autotransc.cmo

autotransc.cmx: common.cmx
autotransc_main.cmx: autotransc.cmx

autotransc.cmo autotransc.cmx: autotransc.ml common.cmi

# ------------------------------------

autotransd.byte: ZLEXTRALIBS = $(ZLGTKLIBS)
autotransd.byte: ZELUCFLAGS += -gtk2
autotransd.byte: maneuvers.cmo utils.cmo consts.cmo common.cmo \
    		 autotransd.cmo autotransd_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ \
	    $(ZLSTDLIBS) $(ZLEXTRALIBS) \
			$(INCLUDES) $^

autotransd.opt: ZLEXTRALIBS = $(ZLGTKLIBS)
autotransd.opt: ZELUCFLAGS += -gtk2
autotransd.opt: maneuvers.cmx utils.cmx consts.cmx common.cmx \
    		 autotransd.cmx autotransd_main.cmx
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ \
	    $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) \
			$(INCLUDES:.cma=.cmxa) $^

autotransd.ml autotransd_main.ml: autotransd.zls common.zci
	$(ZELUC) $(ZELUCFLAGS) $(ZELUCEXTRAFLAGS) -s main $<
	mv main.ml autotransd_main.ml

autotransd.cmo: common.cmo
autotransd_main.cmo: autotransd.cmo

autotransd.cmx: common.cmx
autotransd_main.cmx: autotransd.cmx

autotransd.cmi autotransd.cmo autotransd.cmx: INCLUDES += $(LABLGTK2)
autotransd.cmo autotransd.cmx: autotransd.ml common.cmi

# ------------------------------------

common.ml: common.zls consts.zci utils.zci
	$(ZELUC) $(ZELUCFLAGS) $<
common.cmx common.cmo common.cmi common.zci: common.ml consts.cmi utils.cmi

# ------------------------------------

consts.cmx consts.cmo consts.cmi: consts.ml
draw.cmx draw.cmo draw.cmi: draw.ml
utils.cmx utils.cmo utils.cmi: utils.ml

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
	$(MAKE) -C spec clean

realclean cleanall: clean
	-@rm -f autotransc.byte autotransc.opt
	-@rm -f autotrans_gui.byte autotrans_gui.opt
	-@rm -f autotransd.byte autotransd.opt
	$(MAKE) -C spec cleanall
