include ../config

ZLC = ../bin/zlc.$(TARGET)

LOBJ = pervasives.lci \
       char.lci \
       complex.lci \
       int32.lci \
       nativeint.lci \
       int64.lci \
       random.lci \
       string.lci \
       graphics.lci \
       zlsolve.lci \
       basics.lci

LOBJ_GTK = $(LOBJ) \
	   gtkplot.lci

INCLUDES += -I solvers
SOLVER_OBJS = solvers/fixedstep.cmo \
	      solvers/illinois.cmo  \
	      solvers/rk4.cmo       \
	      solvers/odexx.cmo     \
	      $(OPTIONAL_SOLVER_OBJS)

OBJ = solvers.cmo \
      zlsolve.cmo \
      basics.cmo \
      $(SOLVER_OBJS) \
      loadsolvers.cmo \
      dump.cmo

OBJ_GTK = reactpanel.cmo \
	  gtkplot.cmo \
	  scope.cmo

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

pervasives.lci: ZLCFLAGS := -nopervasives
zlsolve.lci: zlsolve.lsi pervasives.lci

basics.lci: basics.lsi pervasives.lci

zlsolve.lci: zlsolve.lsi

solvers/solversundials.cmo: INCLUDES += $(SUNDIALS)
solvers/solversundials.cmx: INCLUDES += $(SUNDIALS)

reactpanel.cmo: INCLUDES += $(LABLGTK2)
reactpanel.cmx: INCLUDES += $(LABLGTK2)

gtkplot.lci: gtkplot.lsi pervasives.lci
gtkplot.cmi:
gtkplot.cmo: INCLUDES += $(LABLGTK2)
gtkplot.cmx: INCLUDES += $(LABLGTK2)

scope.ml: scope.ls gtkplot.lci basics.lci
	$(ZLC) $(ZLCFLAGS) scope.ls

dump.ml: dump.ls basics.lci
	$(ZLC) $(ZLCFLAGS) dump.ls

loadsolvers.ml:
	@echo "(* initialize solvers *)" > $@
	@for s in $(notdir $(SOLVER_OBJS:.cmo=)); do		\
	    echo "let m = String.capitalize \"$$s\""            \
	    	 "in Printf.eprintf \"module %s = %s\n\" m m;;" \
		 | $(OCAML) 1>/dev/null 2>>$@; 			\
	done
	@echo "let () = Zlsolve.set_default_solver \"$(SOLVER)\";;" >> $@

### Generating a Zelus in numbers tables
# Download ocamlwc from: http://www.lri.fr/~filliatr/software.en.html
loc:
	@echo "Simulation algorithm"
	@ocamlwc -c zlsolve.ml basics.ml
	@echo "Solver interface (generic)"
	@ocamlwc -c solvers.ml
	@echo "Solver interface (Sundials, compiler specific)"
	@ocamlwc -c solvers/solversundials.ml
	@echo "Zero-crossing detection (Illinois)"
	@ocamlwc -c solvers/illinois.ml

depend: .depend
.depend: *.mli *.ml
	@$(OCAMLDEP) $(INCLUDES) *.mli *.ml solvers/*.mli solvers/*.ml > .depend

clean:
	-@rm -f *.cm[iox] *.annot *~ *.o
	-@rm -f scope.ml scope.obc
	-@rm -f dump.ml dump.obc
	-@rm -f *.lci *.cma *.cmxa *.a
	-@rm -f solvers/*.cm[iox] solvers/*.annot solvers/*~ solvers/*.o
	-@rm -f loadsolvers.ml

realclean cleanall: clean

-include .depend
