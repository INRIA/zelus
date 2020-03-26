include ../../config

EXAMPLE=ball.zls autoball.zls flatball.zls
ML=showball.ml world.ml

ZLEXTRALIBS = $(ZLGTKLIBS)

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

ball.byte: showball.cmo world.cmo ball.cmo ball_main.cmo
	$(OCAMLFIND) $(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	  	-I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) $^ \
	-package graphics -linkpkg

ball.opt: showball.cmx world.cmx ball.cmx ball_main.cmx
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) graphics.cmxa \
	    $(ZLEXTRALIBS:.cma=.cmxa) $^

showball.cmo : showball.ml
	$(OCAMLFIND) $(OCAMLC) -c showball.ml -package graphics

showball.cmx : showball.ml
	$(OCAMLFIND) $(OCAMLOPT) -c showball.ml -package graphics

ball_main.cmo: INCLUDES += $(SUNDIALS)
ball_main.cmx: INCLUDES += $(SUNDIALS)

ball.ml ball_main.ml: showball.zci world.zci ball.zls
	$(ZELUC) $(ZELUCFLAGS) -s main ball.zls
	mv main.ml ball_main.ml

#

autoball.byte: showball.cmo world.cmo ball.cmo autoball.cmo autoball_main.cmo
	$(OCAMLFIND) $(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) $^  \
	-package graphics -linkpkg

autoball.opt: showball.cmx world.cmx ball.cmx autoball.cmx autoball_main.cmx
	$(OCAMLFIND) $(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) \
	    graphics.cmxa $(ZLEXTRALIBS:.cma=.cmxa) $^   \
	-package graphics -linkpkg

autoball.ml autoball_main.ml: showball.zci world.zci autoball.zls
	$(ZELUC) $(ZELUCFLAGS) -s main autoball.zls
	mv main.ml autoball_main.ml

#

flatball.byte: showball.cmo flatworld.cmo flatball.cmo flatball_main.cmo
	$(OCAMLFIND) $(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) $^  \
	-package graphics -linkpkg

flatball.opt: showball.cmx flatworld.cmx flatball.cmx flatball_main.cmx
	$(OCAMLFIND) $(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) \
	    $(ZLEXTRALIBS:.cma=.cmxa) $^  \
	-package graphics -linkpkg

flatball_main.cmo: INCLUDES += $(SUNDIALS)
flatball_main.cmx: INCLUDES += $(SUNDIALS)

flatball.ml flatball_main.ml: showball.zci flatworld.zci flatball.zls
	$(ZELUC) $(ZELUCFLAGS) -s main flatball.zls
	mv main.ml flatball_main.ml

#

spec: spec_byte spec_opt spec_plot_byte spec_plot_opt
spec_byte: byte spec.byte
spec_opt: opt spec.opt
spec_plot_byte: byte spec_plot.byte
spec_plot_opt: opt spec_plot.opt

spec_plot.ml: ZLEXTRALIBS += $(EXAMPLE:.zls=.cmo)
spec_plot.ml: ZELUCFLAGS += -gtk2

spec.byte: showball.cmo flatworld.cmo flatball.cmo spec.cmo spec_main.ml
	$(OCAMLFIND) $(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS)  $^  \
	-package graphics -linkpkg

spec.opt: showball.cmx flatworld.cmx flatball.cmx spec.cmx spec_main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) $^  \
	-package graphics -linkpkg

spec_plot.byte: showball.cmo flatworld.cmo flatball.cmo spec.cmo spec_plot.ml
	$(OCAMLFIND) $(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) $^  \
	-package graphics -linkpkg

spec_plot.opt: showball.cmx flatworld.cmx flatball.cmx spec.cmx spec_plot.ml
	$(OCAMLFIND) $(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) $^  \
	-package graphics -linkpkg

spec_%.ml: spec.zls
	$(ZELUC) $(ZELUCFLAGS) -o $(<:.zls=)_$(@:spec_%.ml=%) -s $(@:spec_%.ml=%) $<
%.ml: %.zls
	$(ZELUC) $(ZELUCFLAGS) -o $(<:.zls=)_main -s main $<


# ##

depend: .depend
.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

export:
	mkdir $(DISTDIR)/bouncingball
	cp autoball.zls ball.zls Makefile readme.md \
	   showball.zli showball.ml showball.mli \
	   show.zli show.mli world.zli world.ml world.mli \
	   flatball.zls flatworld.ml flatworld.mli flatworld.zli \
	   $(DISTDIR)/bouncingball/
	mkdir $(DISTDIR)/bouncingball/img
	cp img/*.png $(DISTDIR)/bouncingball/img/

clean:
	-@rm -f ball_main.ml ball.ml
	-@rm -f autoball_main.ml autoball.ml
	-@rm -f flatball_main.ml flatball.ml
	-@rm -f spec_main.ml spec_plot.ml spec.ml
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci
	-@rm -f $(EXAMPLE:%.zls=%.byte) $(EXAMPLE:%.zls=%.opt)
	-@rm -f .depend

realclean cleanall: clean

-include .depend
