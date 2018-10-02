include ../../config

.PHONY: test debug

ZLEXTRALIBS = $(ZLGTKLIBS)

default: $(word 1, $(targets))
all:  $(targets)
byte: autotrans_test.byte autotrans_w_control.byte autotransd.byte

# ------------------------------------

autotrans_w_control.byte: INCLUDES += $(LABLGTK2) $(SUNDIALS)
autotrans_w_control.byte: ZELUCFLAGS += -gtk2 -nodeadcode
autotrans_w_control.byte: utils.cmo consts.cmo draw.cmo common.cmo \
    		 autotrans_core.cmo autotrans_w_control.cmo autotrans_w_control_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) graphics.cma $(ZLGTKLIBS) $^

autotrans_w_control.ml autotrans_w_control_main.ml: autotrans_w_control.zls \
				 autotrans_core.zci draw.zci common.zci
	$(ZELUC) $(ZELUCFLAGS) $(ZELUCEXTRAFLAGS) -s main $<
	mv main.ml autotrans_w_control_main.ml

autotrans_w_control.cmi autotrans_w_control.cmo: INCLUDES += $(LABLGTK2)
autotrans_w_control.cmo: autotrans_w_control.ml \
				 autotrans_core.cmi draw.cmi common.cmi

# ------------------------------------

autotrans_test.byte: INCLUDES += $(LABLGTK2) $(SUNDIALS)
autotrans_test.byte: ZELUCFLAGS += -gtk2
autotrans_test.byte: utils.cmo consts.cmo common.cmo \
    		 autotrans_core.cmo autotrans_test.cmo autotrans_test_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) $(ZLGTKLIBS) $^

autotrans_test.ml autotrans_test_main.ml: autotrans_test.zls \
         autotrans_core.zci common.zci
	$(ZELUC) $(ZELUCFLAGS) $(ZELUCEXTRAFLAGS) -s main $<
	mv main.ml autotrans_test_main.ml

autotrans_test.cmi autotrans_test.cmo: INCLUDES += $(LABLGTK2)
autotrans_test.cmo: autotrans_test.ml \
			 	 autotrans_core.cmi common.cmi

# ------------------------------------

autotransd.byte: INCLUDES += $(LABLGTK2) $(SUNDIALS)
autotransd.byte: ZELUCFLAGS += -gtk2
autotransd.byte: utils.cmo consts.cmo common.cmo \
    		 autotransd.cmo autotransd_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) $(ZLGTKLIBS) $^

autotransd.ml autotransd_main.ml: autotransd.zls \
				 common.zci
	$(ZELUC) $(ZELUCFLAGS) $(ZELUCEXTRAFLAGS) -s main $<
	mv main.ml autotransd_main.ml

autotransd.cmi autotransd.cmo: INCLUDES += $(LABLGTK2)
autotransd.cmo: autotransd.ml \
				 common.cmi

# ------------------------------------

autotrans_core.ml: autotrans_core.zls
	$(ZELUC) $(ZELUCFLAGS) $<
autotrans_core.cmo autotrans_core.cmi autotrans_core.zci: autotrans_core.ml

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
	-@rm -f autotrans_test_main.ml autotrans_test.ml
	-@rm -f autotrans_w_control_main.ml autotrans_w_control.ml
	-@rm -f autotransd_main.ml autotransd.ml
	-@rm -f autotrans_core.ml common.ml
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci
	-@rm -f autotrans_test.byte autotrans_test.opt
	-@rm -f autotrans_w_control.byte autotrans_w_control.opt
	-@rm -f autotransd.byte autotransd.opt
