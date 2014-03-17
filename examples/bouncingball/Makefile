include ../../config

EXAMPLE=ball.zls autoball.zls
ML=showball.ml world.ml

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

ball.byte: showball.cmo world.cmo ball.cmo ball_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) graphics.cma $(ZLEXTRALIBS) $^

ball.opt: showball.cmx world.cmx ball.cmx ball_main.cmx
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) graphics.cmxa \
	    $(ZLEXTRALIBS:.cma=.cmxa) $^

ball_main.cmo: INCLUDES += $(SUNDIALS)
ball_main.cmx: INCLUDES += $(SUNDIALS)

ball.ml ball_main.ml: showball.zci world.zci ball.zls
	$(ZELUC) $(ZELUCFLAGS) -s main ball.zls
	mv main.ml ball_main.ml

#

autoball.byte: showball.cmo world.cmo ball.cmo autoball.cmo autoball_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) graphics.cma $(ZLEXTRALIBS) $^

autoball.opt: showball.cmx world.cmx ball.cmx autoball.cmx autoball_main.cmx
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) \
	    $(ZLEXTRALIBS:.cma=.cmxa) $^

autoball.ml autoball_main.ml: showball.zci world.zci autoball.zls
	$(ZELUC) $(ZELUCFLAGS) -s main autoball.zls
	mv main.ml autoball_main.ml

# ##

depend: .depend
.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

export:
	mkdir $(DISTDIR)/bouncingball
	cp autoball.zls ball.zls Makefile readme.md \
	   showball.zli showball.ml showball.mli \
	   show.zli show.mli world.zli world.ml world.mli \
	   $(DISTDIR)/bouncingball/
	mkdir $(DISTDIR)/bouncingball/img
	cp img/*.png $(DISTDIR)/bouncingball/img/

clean:
	-@rm -f ball_main.ml ball.ml autoball_main.ml
	-@rm -f autoball.ml
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci
	-@rm -f $(EXAMPLE:%.zls=%.byte) $(EXAMPLE:%.zls=%.opt)
	-@rm -f .depend

realclean cleanall: clean

-include .depend
