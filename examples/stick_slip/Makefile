include ../../config

INCLUDES += graphics.cma

all:stick_slip.byte

stick_slip.byte: stick_slip.ml stick_slip_main.ml

stick_slip_main.ml stick_slip.ml: stick_slip.zls
	$(ZELUC) $(ZELUCFLAGS) -s main $<
	mv main.ml $(<:%.zls=%_main.ml)

clean:
	rm -f stick_slip.byte stick_slip.opt
	rm -f stick_slip.ml stick_slip_main.ml
	rm -f *.cm[iox]
	rm -f *.zci
	rm -f *.o
	rm -f *.annot

realclean cleanall: clean

depend: *.mli *.ml
	$(OCAMLDEP) $(INCLUDES) $^ > .depend

include .depend
