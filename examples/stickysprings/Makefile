include ../../config

ZLEXTRALIBS = $(ZLGTKLIBS)

EXAMPLE=stickysprings.zls

default: $(word 1, $(targets))
all:  $(targets)
byte: stickysprings.byte stickysprings3d.byte
opt:  stickysprings.opt stickysprings3d.opt

ifeq ($(GLMLITE_ENABLED), 1)

stickysprings3d.byte: INCLUDES += -I +lablgtk2 $(SUNDIALS) $(GLMLITE)
stickysprings3d.byte: ZLEXTRALIBS += GL.cma Glu.cma Glut.cma GLE.cma
stickysprings3d.byte: world.cmo stickysprings.ml stickysprings3d.ml stickysprings3d_main.ml
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) $^

stickysprings3d.opt: INCLUDES += -I +lablgtk2 $(SUNDIALS) $(GLMLITE)
stickysprings3d.opt: ZLEXTRALIBS += GL.cmxa Glu.cmxa Glut.cmxa GLE.cmxa
stickysprings3d.opt: world.cmx stickysprings.ml stickysprings3d.ml stickysprings3d_main.ml
	$(OCAMLOPT) $(OCAMLFLAGS) -o $@ $(INCLUDES) -I $(ZLLIB) \
	    $(ZLSTDLIBS:%.cma=%.cmxa) $(ZLEXTRALIBS:%.cma=%.cmxa) $^

stickysprings3d.ml sticksprings3d_main.ml: stickysprings3d.zls stickysprings.zci world.zci
	$(ZELUC) $(ZELUCFLAGS) -gtk2 -s main $<
	mv main.ml stickysprings3d_main.ml

world.cmi: world.mli

world.cmo: INCLUDES += $(GLMLITE)
world.cmo: world.ml world.cmi

world.cmx: INCLUDES += $(GLMLITE)
world.cmx: world.ml world.cmi

world.zci: world.zli

testworld: world.cmi world.cmo testworld.ml
	$(OCAMLC) -o $@ unix.cma bigarray.cma \
	    -I $(GLMLITE) GL.cma Glu.cma Glut.cma GLE.cma \
	    world.cmo testworld.ml

else

stickysprings3d.byte:
	@printf "$@: glMLite is not available\n"

stickysprings3d.opt:
	@printf "$@: glMLite is not available\n"

endif

export:
	mkdir $(DISTDIR)/stickysprings
	cp Makefile readme.md \
	   stickysprings3d.zls stickysprings.zls \
	   world.zli world.ml world.mli \
	   $(DISTDIR)/stickysprings/
	mkdir $(DISTDIR)/stickysprings/img
	cp img/*.png $(DISTDIR)/stickysprings/img/

clean:
	-@rm -f $(EXAMPLE:.zls=.ml) $(EXAMPLE:.zls=_main.ml)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci
	-@rm -f $(EXAMPLE:%.zls=%.byte) $(EXAMPLE:%.zls=%.opt)
	-@rm -f stickysprings3d.ml stickysprings3d_main.ml
	-@rm -f testworld stickysprings3d.byte stickysprings3d.opt

realclean cleanall: clean

# Common rules
.SUFFIXES : .ml .zls .zci

%.ml %.zci: %.zls
	# $(ZELUC) $(ZELUCFLAGS) -s main -sampling 50 -gtk2 $<
	$(ZELUC) $(ZELUCFLAGS) -s main -sampling 9 -gtk2 $<
	mv main.ml $(<:.zls=)_main.ml

