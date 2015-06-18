include ../../config

EXAMPLE=ball_spring.zls

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

ball_spring.byte: ZLEXTRALIBS += graphics.cma $(OBJ)
ball_spring.byte: $(OBJ)

ball_spring.opt: ZLEXTRALIBS += graphics.cmxa $(OBJ:.cmo=.cmx)
ball_spring.opt: $(OBJ:%.cmo=%.cmx)

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
	-@rm -f *~ *.cmi *.cmo *.cmx *.annot *.o *.zci *.obc *.ml *.out *.byte *.opt
	-@rm -f ball_spring.ps

realclean cleanall: clean
	-@rm -f $(EXAMPLE:%.zls=%.opt) $(EXAMPLE:%.zls=%.byte)

# Common rules
.SUFFIXES : .ml .zls .byte

.zls.ml:
	$(ZELUC) $(ZELUCFLAGS) -s main $<
	mv main.ml $(<:.zls=)_main.ml

