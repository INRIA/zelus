include ../../config

ZLEXTRALIBS = $(ZLGTKLIBS)

EXAMPLE=stickysprings.ls

default: $(word 1, $(targets))
all:  $(targets)
byte: stickysprings.byte stickysprings3d.byte
opt:  stickysprings.opt stickysprings3d.opt

ifeq ($(GLMLITE_ENABLED), 1)

stickysprings3d.byte: INCLUDES += -I +lablgtk2 $(SUNDIALS) $(GLMLITE)
stickysprings3d.byte: ZLEXTRALIBS += GL.cma GLE.cma Glu.cma Glut.cma
stickysprings3d.byte: world.cmo stickysprings.ml stickysprings3d.ml stickysprings3d_main.ml
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) $^

stickysprings3d.opt: INCLUDES += -I +lablgtk2 $(SUNDIALS) $(GLMLITE)
stickysprings3d.opt: ZLEXTRALIBS += GL.cmxa GLE.cmxa Glu.cmxa Glut.cmxa
stickysprings3d.opt: world.cmx stickysprings.ml stickysprings3d.ml stickysprings3d_main.ml
	$(OCAMLOPT) $(OCAMLFLAGS) -o $@ $(INCLUDES) -I $(ZLLIB) \
	    $(ZLSTDLIBS:%.cma=%.cmxa) $(ZLEXTRALIBS:%.cma=%.cmxa) $^

stickysprings3d.ml sticksprings3d_main.ml: stickysprings3d.ls stickysprings.lci world.lci
	$(ZLC) $(ZLCFLAGS) -period -gtk2 -sampling 9 -s main $<
	mv main.ml stickysprings3d_main.ml

world.cmi: world.mli

world.cmo: INCLUDES += $(GLMLITE)
world.cmo: world.ml world.cmi

world.cmx: INCLUDES += $(GLMLITE)
world.cmx: world.ml world.cmi

world.lci: world.lsi

testworld: world.cmi world.cmo testworld.ml
	$(OCAMLC) -o $@ unix.cma bigarray.cma \
	    -I $(GLMLITE) GL.cma GLE.cma Glu.cma Glut.cma \
	    world.cmo testworld.ml

else

stickysprings3d.byte:
	@echo "$@: glMLite is not available"

stickysprings3d.opt:
	@echo "$@: glMLite is not available"

endif

export:
	mkdir $(DISTDIR)/stickysprings
	cp Makefile readme.md \
	   stickysprings3d.ls stickysprings.ls \
	   world.lsi world.ml world.mli \
	   $(DISTDIR)/stickysprings/
	mkdir $(DISTDIR)/stickysprings/img
	cp img/*.png $(DISTDIR)/stickysprings/img/

clean:
	-@rm -f $(EXAMPLE:.ls=.ml) $(EXAMPLE:.ls=_main.ml)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.lci
	-@rm -f $(EXAMPLE:%.ls=%.byte) $(EXAMPLE:%.ls=%.opt)
	-@rm -f stickysprings3d.ml stickysprings3d_main.ml
	-@rm -f testworld stickysprings3d.byte stickysprings3d.opt

realclean cleanall: clean

# Common rules
.SUFFIXES : .ml .ls .lci

%.ml %.lci: %.ls
	# $(ZLC) $(ZLCFLAGS) -s main -sampling 50 -gtk2 $<
	$(ZLC) $(ZLCFLAGS) -period -s main -sampling 9 -gtk2 $<
	mv main.ml $(<:.ls=)_main.ml

