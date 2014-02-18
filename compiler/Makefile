#************************************************************************#
#                                                                        #
#  The Zelus Hybrid Synchronous Language                                 #
#  Copyright (C) 2012-2013                                               #
#                                                                        #
#  Timothy Bourke                                                        #
#  Marc Pouzet                                                           #
#                                                                        #
#  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   #
#                                                                        #
#   This file is distributed under the terms of the CeCILL-C licence     #
#                                                                        #
#************************************************************************#
include ../config

GENSOURCES = parsing/parser.ml parsing/parser.mli parsing/lexer.ml

INCLUDES += $(DIRECTORIES:%=-I %)

LOCATION = global/location.cmo	

PARSING = parsing/parsetree.cmo \
	parsing/lexer.cmo \
	parsing/parser.cmo

GLOBAL = global/misc.cmo \
	global/pp_tools.cmo \
	global/ident.cmo \
	global/lident.cmo \
	global/deftypes.cmo \
	global/defcaus.cmo \
	global/definit.cmo \
	global/zelus.cmo \
	global/vars.cmo \
	global/global.cmo \
	global/modules.cmo \
	global/initial.cmo \
	global/ptypes.cmo \
	global/printer.cmo \
	global/scoping.cmo \
	global/graph.cmo \

TYPING = typing/types.cmo \
	typing/typerrors.cmo \
	typing/interface.cmo \
	typing/total.cmo \
	typing/matching.cmo \
	typing/patternsig.cmo \
	typing/typing.cmo

ANALYSIS = analysis/causal.cmo \
	analysis/causality.cmo \
	analysis/newcausal.cmo \
	analysis/newcausality.cmo \
	analysis/init.cmo \
	analysis/initialization.cmo

REWRITE = rewrite/dependences.cmo \
	rewrite/automata.cmo \
        rewrite/activate.cmo \
	rewrite/letin.cmo \
	rewrite/periodz.cmo \
	rewrite/goagain.cmo \
	rewrite/present.cmo \
	rewrite/inline.cmo \
	rewrite/ode.cmo \
	rewrite/period.cmo \
	rewrite/write.cmo \
	rewrite/completion.cmo \
	rewrite/reset.cmo \
	rewrite/last.cmo \
	rewrite/aform.cmo \
	rewrite/cse.cmo \
	rewrite/deadcode.cmo \
	rewrite/control.cmo \
	rewrite/schedule.cmo \
	rewrite/copy.cmo

GENCODE = gencode/obc.cmo \
	gencode/oprinter.cmo \
	gencode/translate.cmo \
	gencode/copystate.cmo

MAIN = main/compiler.cmo \
	main/simulator.cmo \
	main/fixstep.cmo \
	main/main.cmo

OBJ = $(LOCATION) $(PARSING) $(GLOBAL) $(TYPING) $(ANALYSIS) \
	$(REWRITE) $(GENCODE) $(MAIN)

default: $(word 1, $(targets))
world: all

all: $(targets)

opt: $(BIN).opt
byte: $(BIN).byte

$(BIN).opt: $(GENSOURCES) $(OBJ:%.cmo=%.cmx)
	$(OCAMLOPT) $(UNIXX) $(OCAMLOPTFLAGS) $(INCLUDES) \
	-I $(MENHIRLIB) menhirLib.cmx $(OBJ:%.cmo=%.cmx) -o $(BIN).opt

$(BIN).byte: $(GENSOURCES) $(OBJ)
	$(OCAMLC) $(UNIX) $(OCAMLFLAGS) $(INCLUDES) \
        -I $(MENHIRLIB) menhirLib.cmo $(OBJ) -o $(BIN).byte

debug: OCAMLFLAGS += -g
debug: byte debugprinter.cma

debugprinter.cma: $(LOCATION) $(GLOBAL) gencode/obc.cmo gencode/oprinter.cmo
	$(OCAMLC) -a -o $@ $^

# Extra dependences

global/misc.cmo global/misc.cmi: OCAMLFLAGS := \
		-pp "$(CPP) $(CPPFLAGS) \
		     -DSTDLIB=\\\"$(libdir)\\\" \
		     -DSOLVER=\\\"$(SOLVER)\\\" \
                     -DDATE=\\\"\"`date`\"\\\""


global/misc.cmx global/misc.cmi: OCAMLOPTFLAGS := \
		-pp "$(CPP) $(CPPFLAGS) \
		     -DSTDLIB=\\\"$(libdir)\\\" \
		     -DSOLVER=\\\"$(SOLVER)\\\" \
                     -DDATE=\\\"\"`date`\"\\\""

parsing/parser.cmo parsing/parser.cmi: INCLUDES := -I $(MENHIRLIB) $(INCLUDES)

parsing/parser.cmx parsing/parser.cmi: INCLUDES := -I $(MENHIRLIB) $(INCLUDES)

.PHONY: tags
tags:
	$(OTAGS) -o tags $(DIRECTORIES:%=%/*.ml)

depend: .depend

.depend: $(GENSOURCES)
	$(OCAMLDEP) $(INCLUDES) \
	    $(DIRECTORIES:%=%/*.mli) $(DIRECTORIES:%=%/*.ml) \
	    > .depend

ML = $(OBJ:.cmo=.ml)

wc:
	wc $(ML)

### Making documentation from the code
# documentation goes in ../doc/lucyc and is not cleaned up by clean
tex: $(GENSOURCES)
	mkdir -p ../doc/lucyc
	$(OCAMLWEB) $(subst parsing/lexer.ml,--impl parsing/lexer.mll, \
		  $(subst parsing/parser.ml,--impl parsing/parser.mly, \
		    $(OBJ:.cmo=.ml))) > ../doc/lucyc/lucyc.tex

### Generating a Zelus in numbers tables
# Download ocamlwc from: http://www.lri.fr/~filliatr/software.en.html
loc:
	@echo "Main driver (incl. main data structures)"
	@ocamlwc -c main/compiler.ml main/main.ml main/simulator.ml \
		global/global.ml global/graph.ml global/misc.ml \
		global/lident.ml global/ident.ml global/initial.ml \
		global/modules.ml global/scoping.ml global/vars.ml
	@echo "Abstract syntax and pretty printers"
	@ocamlwc -c global/hybrid.ml global/deftypes.ml global/location.ml \
		global/pp_tools.ml global/printer.ml global/ptypes.ml
	@echo "Lexer \\& parser"
	@ocamlwc -c parsing/parser.mly parsing/lexer.mll
	@echo "Typing"
	@ocamlwc -c typing/*.ml
	@echo "Initialization and causality analysis"
	@ocamlwc -c analysis/*.ml
	@echo "Transformation of hybrid features"
	@ocamlwc -c rewrite/ode.ml rewrite/goagain.ml rewrite/last.ml \
	    	rewrite/period.ml
	@echo "Transformation of automata"
	@ocamlwc -c rewrite/automata.ml
	@echo "Transformation of synchronous features"
	@ocamlwc -c rewrite/activate.ml rewrite/aform.ml rewrite/completion.ml \
	    	rewrite/control.ml rewrite/dependences.ml rewrite/letin.ml \
		rewrite/present.ml rewrite/reset.ml rewrite/schedule.ml \
		rewrite/write.ml
	@echo "Inlining and other optimizations"
	@ocamlwc -c rewrite/copy.ml rewrite/deadcode.ml rewrite/inline.ml \
	    	rewrite/cse.ml
	@echo "Code generation"
	@ocamlwc -c gencode/*.ml

dvi: tex
	(cd ../doc/lucyc; $(LATEX) lucyc.tex; $(LATEX) lucyc.tex; \
	 mv lucyc.dvi ..)

doc: dvi

html: tex
	(cd ../doc/lucyc; $(HEVEA) ocamlweb.sty lucyc.tex; \
	 $(HEVEA) ocamlweb.sty lucyc.tex; \
	 $(HACHA) lucyc.html)


# cleaning:
clean:
	-rm -f .depend
	(for d in $(DIRECTORIES); \
	 do rm -f $$d/*.annot $$d/*.cm[iox] $$d/*.o; \
	 done; \
	 rm -f $(BIN).byte $(BIN).opt debugprinter.cma \
           $(GENSOURCES) parsing/parser.conflicts)

realclean cleanall: clean

-include .depend
