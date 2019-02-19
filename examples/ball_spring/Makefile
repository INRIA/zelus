include ../../config

EXAMPLE=ball_spring.zls
ZLEXTRALIBS = $(ZLGTKLIBS)

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

ball_spring.byte: ZLEXTRALIBS += graphics.cma $(OBJ)
ball_spring.byte: $(OBJ)

ball_spring.opt: ZLEXTRALIBS += graphics.cmxa $(OBJ:.cmo=.cmx)
ball_spring.opt: $(OBJ:%.cmo=%.cmx)

spec: spec_byte spec_opt spec_plot_byte spec_plot_opt
spec_byte: byte spec.byte
spec_opt: opt spec.opt
spec_plot_byte: byte spec_plot.byte
spec_plot_opt: opt spec_plot.opt

spec_plot.ml: ZLEXTRALIBS += $(EXAMPLE:.zls=.cmo)
spec_plot.ml: ZELUCFLAGS += -gtk2

spec.byte: ball_spring.cmo spec.cmo spec_main.ml
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) graphics.cma \
	    $^
spec.opt: ball_spring.cmx spec.cmx spec_main.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) graphics.cmxa \
	    $^

spec_plot.byte: ball_spring.cmo spec.cmo spec_plot.ml
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) graphics.cma \
	    $^
spec_plot.opt: ball_spring.cmx spec.cmx spec_plot.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) graphics.cmxa \
	    $^

ball_spring.out: ball_spring.byte
	./ball_spring.byte -maxt 25 -fullspeed

img/ball_spring_plot.png: ball_spring_png.gplot ball_spring.out
	gnuplot < $< > $@

ball_spring.ps: ball_spring.gplot ball_spring.out
	gnuplot < $< > $@

img/ball_spring.pdf: ball_spring.ps
	pstopdf $< -o $@

export:
	mkdir $(DISTDIR)/ball_spring
	cp ball_spring.zls ball_spring.gplot Makefile readme.md \
	   $(DISTDIR)/ball_spring/
	mkdir $(DISTDIR)/ball_spring/img
	cp img/*.png $(DISTDIR)/ball_spring/img/
	cp ball_spring.pdf $(DISTDIR)/ball_spring/img/

#

clean:
	-@rm -f *~ *.cmi *.cmo *.cmx *.annot *.o *.zci *.obc *.ml *.out
	-@rm -f ball_spring.ps

realclean cleanall: clean
	-@rm -f *.byte *.opt

# Common rules
.SUFFIXES : .ml .zls .byte

spec_%.ml: spec.zls
	$(ZELUC) $(ZELUCFLAGS) -o $(<:.zls=)_$(@:spec_%.ml=%) -s $(@:spec_%.ml=%) $<
%.ml: %.zls
	$(ZELUC) $(ZELUCFLAGS) -o $(<:.zls=)_main -s main $<
