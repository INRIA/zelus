include ../config

ZELUC = ../compiler/zeluc.$(TARGET)

LOBJ = pervasives.zci \
       char.zci \
       complex.zci \
       int32.zci \
       nativeint.zci \
       int64.zci \
       random.zci \
       string.zci \
       graphics.zci \
       basics.zci

LOBJ_GTK = $(LOBJ) \
	   gtkplot.zci

INCLUDES += -I solvers
SOLVER_OBJS = solvers/illinois.cmo  \
	      solvers/odexx.cmo     \
	      $(OPTIONAL_SOLVER_OBJS)

OBJ = zls.cmo \
      zlsolve.cmo \
      basics.cmo \
      $(SOLVER_OBJS) \
      defaultsolver.cmo \
      dump.cmo \
      zlsrun.cmo

OBJ_GTK = gtkplot.cmo \
	  scope.cmo \
 	  zlsrungtk.cmo

all: $(targets) $(gtktargets)

byte: zllib.cma $(LOBJ)
opt:  zllib.cmxa $(LOBJ)

withgtk.byte: byte zllibgtk.cma  $(LOBJ_GTK) $(OBJ_GTK:.cmo=.cmi)
withgtk.opt:  opt zllibgtk.cmxa $(LOBJ_GTK) $(OBJ_GTK:.cmo=.cmi)

debug: OCAMLFLAGS += -g
debug: $(word 1, $(targets)) $(word 1, $(gtktargets))

zllib.cma: $(OBJ)
	$(OCAMLC)   -a $(OCAMLCFLAGS) -o $@ $^

zllib.cmxa: $(OBJ:.cmo=.cmx)
	$(OCAMLOPT) -a $(OCAMLCFLAGS) -o $@ $^

zllibgtk.cma: $(OBJ) $(OBJ_GTK)
	$(OCAMLC)   -a $(OCAMLCFLAGS) -o $@ $^

zllibgtk.cmxa: $(OBJ:.cmo=.cmx) $(OBJ_GTK:.cmo=.cmx)
	$(OCAMLOPT) -a $(OCAMLCFLAGS) -o $@ $^

pervasives.zci: ZELUCFLAGS := -nopervasives

basics.zci: basics.zli pervasives.zci

solvers/sundials_cvode.cmo: INCLUDES += $(SUNDIALS) $(SUNDIALS_CVODE)
solvers/sundials_cvode.cmx: INCLUDES += $(SUNDIALS) $(SUNDIALS_CVODE)

zlsrungtk.cmo: INCLUDES += $(LABLGTK2)
zlsrungtk.cmx: INCLUDES += $(LABLGTK2)

gtkplot.zci: gtkplot.zli pervasives.zci
gtkplot.cmi:
gtkplot.cmo: INCLUDES += $(LABLGTK2)
gtkplot.cmx: INCLUDES += $(LABLGTK2)

scope.ml: scope.zls gtkplot.zci basics.zci
	$(ZELUC) $(ZELUCFLAGS) scope.zls

dump.ml: dump.zls basics.zci
	$(ZELUC) $(ZELUCFLAGS) dump.zls

defaultsolver.ml: ../config
	@printf "(* This file is generated automatically by make. *)\n" > $@
	@printf "include $(SOLVER)\n" >> $@

depend: .depend
.depend: *.mli *.ml
	@$(OCAMLDEP) $(INCLUDES) *.mli *.ml solvers/*.mli solvers/*.ml > .depend

clean:
	-@rm -f *.cm[iox] *.annot *~ *.o
	-@rm -f scope.ml scope.obc
	-@rm -f dump.ml dump.obc
	-@rm -f *.zci *.cma *.cmxa *.a
	-@rm -f solvers/*.cm[iox] solvers/*.annot solvers/*~ solvers/*.o
	-@rm -f defaultsolver.ml

realclean cleanall: clean

-include .depend
