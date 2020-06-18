#######################################################################
#                                                                     #
#                                                                     #
#          Zelus, a synchronous language for hybrid systems           #
#                                                                     #
#  (c) 2020 Inria Paris (see the AUTHORS file)                        #
#                                                                     #
#  Copyright Institut National de Recherche en Informatique et en     #
#  Automatique. All rights reserved. This file is distributed under   #
#  the terms of the INRIA Non-Commercial License Agreement (see the   #
#  LICENSE file).                                                     #
#                                                                     #
#######################################################################

include ../config

GENSOURCES = parsing/parser.ml parsing/parser.mli parsing/lexer.ml

INCLUDES += $(DIRECTORIES:%=-I %)

LOCATION = global/location.cmo	

PARSING = parsing/parsetree.cmo \
	parsing/parser.cmo \
	parsing/lexer.cmo

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
	global/zaux.cmo \
	global/ptypes.cmo \
	global/pcaus.cmo \
	global/pinit.cmo \
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
	analysis/init.cmo \
	analysis/initialization.cmo

REWRITE = rewrite/markfunctions.cmo \
	rewrite/static.cmo \
	rewrite/cost.cmo \
	rewrite/inline.cmo \
	rewrite/reduce.cmo \
	rewrite/write.cmo \
	rewrite/unsafe.cmo \
	rewrite/remove_last_in_patterns.cmo \
	rewrite/add_copy_for_last.cmo \
	rewrite/automata.cmo \
        rewrite/activate.cmo \
	rewrite/present.cmo \
	rewrite/period.cmo \
	rewrite/disc.cmo \
	rewrite/pre.cmo \
	rewrite/letin.cmo \
	rewrite/proba.cmo \
	rewrite/complete.cmo \
	rewrite/reset.cmo \
	rewrite/encore.cmo \
	rewrite/horizon.cmo \
	rewrite/aform.cmo \
	rewrite/shared.cmo \
	rewrite/control.cmo \
	rewrite/dependences.cmo \
	rewrite/cse.cmo \
	rewrite/zopt.cmo \
	rewrite/schedule.cmo \
	rewrite/copy.cmo \
	rewrite/deadcode.cmo

GENCODE = gencode/sol.cmo \
	  gencode/cssa.cmo \
	  gencode/obc.cmo \
	  gencode/oaux.cmo \
	  gencode/oprinter.cmo \
	  gencode/ocamlprinter.cmo \
	  gencode/translate.cmo \
	  gencode/inout.cmo	  

VERIF = verif/lmm.cmo \
	verif/plmm.cmo \
	verif/match2condition.cmo \
	verif/zlus2lmm.cmo

MAIN = main/compiler.cmo \
	main/simulator.cmo \
	main/fixstep.cmo

OBJ = $(LOCATION) $(GLOBAL) $(PARSING) $(TYPING) $(ANALYSIS) \
	$(REWRITE) $(GENCODE) $(VERIF) $(MAIN)

default: $(word 1, $(targets))
world: all

all: $(targets)

opt: $(BIN).opt
byte: $(BIN).byte

$(BIN).opt: $(GENSOURCES) $(OBJ:%.cmo=%.cmx) main/main.cmx
	$(OCAMLOPT) $(UNIXX) $(OCAMLOPTFLAGS) $(INCLUDES) \
	-I $(MENHIRLIB) menhirLib.cmxa $(OBJ:%.cmo=%.cmx) main/main.cmx \
	-o $(BIN).opt

$(BIN).byte: $(GENSOURCES) $(OBJ) main/main.cmo
	$(OCAMLC) $(UNIX) $(OCAMLFLAGS) $(INCLUDES) \
        -I $(MENHIRLIB) menhirLib.cma $(OBJ) main/main.cmo \
	-o $(BIN).byte

debug: OCAMLFLAGS += -g
debug: byte debugprinter.cma

debugprinter.cma: $(OBJ)
	$(OCAMLC) -a -o $@ -I $(MENHIRLIB) menhirLib.cma $^

# Extra dependences

global/misc.cmo global/misc.cmi: OCAMLFLAGS := \
		-pp "$(CPP) $(CPPFLAGS) \
		     -DVERSION=\\\"$(VERSION)\\\" \
		     -DSTDLIB=\\\"$(libdir)\\\"   \
		     -DSOLVER=\\\"$(SOLVER)\\\"   \
                     -DDATE=\\\"\"`date`\"\\\""


global/misc.cmx global/misc.cmi: OCAMLOPTFLAGS := \
		-pp "$(CPP) $(CPPFLAGS) \
		     -DVERSION=\\\"$(VERSION)\\\" \
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
	@printf "Main driver (incl. main data structures)\n"
	@ocamlwc -c main/compiler.ml main/main.ml main/simulator.ml \
		global/global.ml global/graph.ml global/misc.ml \
		global/lident.ml global/ident.ml global/initial.ml \
		global/modules.ml global/scoping.ml global/vars.ml
	@printf "Abstract syntax and pretty printers\n"
	@ocamlwc -c global/hybrid.ml global/deftypes.ml global/location.ml \
		global/pp_tools.ml global/printer.ml global/ptypes.ml
	@printf "Lexer \\& parser\n"
	@ocamlwc -c parsing/parser.mly parsing/lexer.mll
	@printf "Typing\n"
	@ocamlwc -c typing/*.ml
	@printf "Initialization and causality analysis\n"
	@ocamlwc -c analysis/*.ml
	@printf "Transformation of hybrid features\n"
	@ocamlwc -c rewrite/ode.ml rewrite/goagain.ml rewrite/last.ml \
	    	rewrite/period.ml
	@printf "Transformation of automata\n"
	@ocamlwc -c rewrite/automata.ml
	@printf "Transformation of synchronous features\n"
	@ocamlwc -c rewrite/activate.ml rewrite/aform.ml rewrite/completion.ml \
	    	rewrite/control.ml rewrite/dependences.ml rewrite/letin.ml \
		rewrite/present.ml rewrite/reset.ml rewrite/schedule.ml \
		rewrite/write.ml
	@printf "Inlining and other optimizations\n"
	@ocamlwc -c rewrite/copy.ml rewrite/deadcode.ml rewrite/inline.ml \
	    	rewrite/cse.ml
	@printf "Code generation\n"
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
