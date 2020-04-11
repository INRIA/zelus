#*************************************************************************)
#                                                                        *)
#                                Zelus                                   *)
#               A synchronous language for hybrid systems                *)
#                       http://zelus.di.ens.fr                           *)
#                                                                        *)
#                    Marc Pouzet and Timothy Bourke                      *)
#                                                                        *)
#  Copyright 2012 - 2019. All rights reserved.                           *)
#                                                                        *)
#  This file is distributed under the terms of the CeCILL-C licence      *)
#                                                                        *)
#  Zelus is developed in the INRIA PARKAS team.                          *)
#                                                                        *)
#*************************************************************************)
include ../config

ZELUC = ../bin/zeluc

LOBJ = stdlib.zci \
       char.zci \
       complex.zci \
       int32.zci \
       nativeint.zci \
       int64.zci \
       random.zci \
       string.zci \
       graphics.zci \
       basics.zci \
       node.zci \
       run.zci


LOBJ_GTK = $(LOBJ) \
	   gtkplot.zci \
	   input.zci

INCLUDES += -I solvers
SOLVER_OBJS = solvers/illinois.cmo  \
	      solvers/odexx.cmo     \
	      $(OPTIONAL_SOLVER_OBJS)

OBJ = zls.cmo \
      basics.cmo \
      zlsolve.cmo \
      lift.cmo \
      $(SOLVER_OBJS) \
      defaultsolver.cmo \
      dump.cmo \
      zlsrun.cmo \
      obs.cmo \
      gen.cmo \
      vbool.cmo \
      run.cmo

OBJ_GTK = gtkplot.cmo \
	  input.cmo \
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

stdlib.zci: ZELUCFLAGS := -nostdlib

basics.zci: basics.zli stdlib.zci

solvers/sundials_cvode.cmo: INCLUDES += $(SUNDIALS) $(SUNDIALS_CVODE)
solvers/sundials_cvode.cmx: INCLUDES += $(SUNDIALS) $(SUNDIALS_CVODE)

zlsrungtk.cmo: INCLUDES += $(LABLGTK2)
zlsrungtk.cmx: INCLUDES += $(LABLGTK2)

gtkplot.zci: gtkplot.zli stdlib.zci
gtkplot.cmi:
gtkplot.cmo: INCLUDES += $(LABLGTK2)
gtkplot.cmx: INCLUDES += $(LABLGTK2)

input.zci: input.zli stdlib.zci
input.cmi:
input.cmo: INCLUDES += $(LABLGTK2)
input.cmx: INCLUDES += $(LABLGTK2)

# extra dependences

random.zci: int32.zci nativeint.zci int64.zci random.zli

obs.ml: obs.zls basics.zci

vbool.ml: vbool.zls

gen.ml: gen.zls random.zci

scope.ml: scope.zls gtkplot.zci basics.zci

dump.ml: dump.zls basics.zci list.zci

defaultsolver.ml: ../config
	@printf "(* This file is generated automatically by make. *)\n" > $@
	@printf "include $(SOLVER)\n" >> $@

depend: .depend
.depend: *.mli *.ml
	@$(OCAMLDEP) $(INCLUDES) *.mli *.ml solvers/*.mli solvers/*.ml > .depend

clean:
	-@rm -f *.cm[iox] *.annot *~ *.o
	-@rm -f scope.ml scope.obc obs.ml obs.obc gen.ml gen.obc dump.ml dump.obc
	-@rm -f *.zci *.cma *.cmxa *.a
	-@rm -f solvers/*.cm[iox] solvers/*.annot solvers/*~ solvers/*.o
	-@rm -f defaultsolver.ml

realclean cleanall: clean

-include .depend
