include ../config

ZELUC = ../bin/zeluc.$(TARGET)

LOBJ = pervasives.zci \
       char.zci \
       complex.zci \
       int32.zci \
       nativeint.zci \
       int64.zci \
       random.zci \
       string.zci \
       graphics.zci \
       zlsolve.zci \
       basics.zci

LOBJ_GTK = $(LOBJ) \
	   gtkplot.zci

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
zlsolve.zci: zlsolve.zli pervasives.zci

basics.zci: basics.zli pervasives.zci

zlsolve.zci: zlsolve.zli

solvers/solversundials.cmo: INCLUDES += $(SUNDIALS)
solvers/solversundials.cmx: INCLUDES += $(SUNDIALS)

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

loadsolvers.ml:
	@printf "(* initialize solvers *)\n" > $@
	@for s in $(notdir $(SOLVER_OBJS:.cmo=)); do		\
	    printf "let m = String.capitalize \"$$s\" %s"            \
	    	   "in Printf.eprintf \"module %s = %s\n\" m m;;\n" \
		 | tee test | $(OCAML) 1>/dev/null 2>>$@; 			\
	done
	@printf "let () = Zlsolve.set_default_solver \"$(SOLVER)\";;\n" >> $@

### Generating a Zelus in numbers tables
# Download ocamlwc from: http://www.lri.fr/~filliatr/software.en.html
loc:
	@printf "Simulation algorithm\n"
	@ocamlwc -c zlsolve.ml basics.ml
	@printf "Solver interface (generic)\n"
	@ocamlwc -c solvers.ml
	@printf "Solver interface (Sundials, compiler specific)\n"
	@ocamlwc -c solvers/solversundials.ml
	@printf "Zero-crossing detection (Illinois)\n"
	@ocamlwc -c solvers/illinois.ml

depend: .depend
.depend: *.mli *.ml
	@$(OCAMLDEP) $(INCLUDES) *.mli *.ml solvers/*.mli solvers/*.ml > .depend

clean:
	-@rm -f *.cm[iox] *.annot *~ *.o
	-@rm -f scope.ml scope.obc
	-@rm -f dump.ml dump.obc
	-@rm -f *.zci *.cma *.cmxa *.a
	-@rm -f solvers/*.cm[iox] solvers/*.annot solvers/*~ solvers/*.o
	-@rm -f loadsolvers.ml

realclean cleanall: clean

-include .depend
