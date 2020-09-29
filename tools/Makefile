include ../config

all:
byte: diff_log zltohtml luciole_zls
opt:
depend .depend:

zltohtml: zltohtml.ml
	$(OCAMLC) -o $@ -I ../compiler/parsing lexer.cmo $^

zltohtml.ml: zltohtml.mll

diff_log: diff_log.ml
	$(OCAMLC) -o $@ str.cma $^

DIRECTORIES = $(shell find ../compiler -mindepth 1 -type d)
INCLUDES += $(DIRECTORIES:%=-I %)
OBJ = \
fixstep.cmo matching.cmo definit.cmo lident.cmo misc.cmo pp_tools.cmo \
location.cmo ident.cmo pinit.cmo deftypes.cmo graph.cmo defcaus.cmo \
parsetree.cmo lmm.cmo pcaus.cmo zelus.cmo vars.cmo control.cmo \
zopt.cmo cse.cmo copy.cmo sol.cmo obc.cmo cssa.cmo global.cmo modules.cmo \
initial.cmo parser.cmo lexer.cmo types.cmo ptypes.cmo zaux.cmo scoping.cmo \
present.cmo horizon.cmo letin.cmo complete.cmo shared.cmo unsafe.cmo reset.cmo \
cost.cmo add_copy_for_last.cmo remove_last_in_patterns.cmo activate.cmo \
period.cmo static.cmo proba.cmo disc.cmo oaux.cmo pre.cmo printer.cmo \
init.cmo causal.cmo typerrors.cmo total.cmo interface.cmo patternsig.cmo \
match2condition.cmo plmm.cmo zlus2lmm.cmo simulator.cmo \
typing.cmo causality.cmo initialization.cmo automata.cmo deadcode.cmo \
write.cmo aform.cmo inline.cmo reduce.cmo dependences.cmo encore.cmo \
markfunctions.cmo oprinter.cmo ocamlprinter.cmo translate.cmo inout.cmo \
schedule.cmo compiler.cmo

luciole_zls: luciole_zls.ml
	$(OCAMLC) -o $@ unix.cma -I $(MENHIRLIB) menhirLib.cma \
	$(INCLUDES) $(OBJ) \
	luciole_zls.ml

clean:
	rm -f *.annot *.cm[iox] *.o
	rm -f zltohtml.ml zltohtml
	rm -f luciole_zls

cleanall: clean
	rm -f zltohtml diff_log
