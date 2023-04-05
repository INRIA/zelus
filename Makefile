all:
	dune build 

debug:
	dune build --debug-backtraces --debug-dependency-path

clean:
	dune clean
#; rm -f *~; (cd zrun/tests; make clean)

wc:
	wc compiler/global/*.ml \
	compiler/typing/*.ml \
	compiler/main/*.ml \
	compiler/parsing/*.mll compiler/parsing/*.mly \
	zrun/*.ml

# OCAMLC = ocamlc
# OCAMLOPT = ocamlopt
# OCAMLDEP = ocamldep
# OCAMLFIND = ocamlfind
# OCAMLFLAG =
# MENHIR = menhir
# MENHIRFLAGS = 
# MENHIRLIB = `$(OCAMLFIND) menhirLib`

# COMPILER_DIR = compiler
# ZRUN_DIR = zrun

# GENSOURCES =
#   $(COMPILER_DIR)/parsing/lexer.mll $(COMPILER_DIR)/parsing/parsing.mly

# COMPILER_BASICS =
#   $(COMPILER_DIR)/$(PARSING) \
#   $(COMPILER_DIR)/$(GLOBAL)

# PARSING = parsing/parsetree.cmo \
# 	parsing/parser.cmo \
# 	parsing/lexer.cmo

# LOCATION = global/location.cmo	

# GLOBAL = global/misc.cmo \
# 	global/pp_tools.cmo \
# 	global/ident.cmo \
# 	global/lident.cmo \
# 	global/deftypes.cmo \
# 	global/defcaus.cmo \
# 	global/definit.cmo \
# 	global/zelus.cmo \
# 	global/vars.cmo \
# 	global/global.cmo \
# 	global/modules.cmo \
# 	global/initial.cmo \
# 	global/aux.cmo \
# 	global/writes.cmo \
# 	global/ptypes.cmo \
# 	global/pcaus.cmo \
# 	global/pinit.cmo \
# 	global/printer.cmo \
# 	global/scoping.cmo \
# 	global/graph.cmo \

# OBJ = $(LOCATION) $(GLOBAL) $(PARSING)


# # main entry
# zrun: zrun.byte zrun.opt

# zrun.byte: $(GENSOURCES) $(OBJ) zrun.cmo
# 	$(OCAMLC) -o zrun.byte \
# 	            -I $(MENHIRLIB) menhirLib.cma \
# 	            $(OBJ) zrun.cmo

# zrun.opt: $(GENSOURCES) $(OBJ:%.cmo=%.cmx) zrun.cmx
# 	$(OCAMLOPT) -o zrun.exe \
# 	            -I $(MENHIRLIB) menhirLib.cmxa \
# 	            $(OBJ:%.cmo=%.cmx) zrun.cmx
# # implicit rules

# .SUFFIXES : .mli .ml .cmi .cmo .cmx .mll .mly .zls .zli .byte .opt

# %.cmi: %.mli
# 	$(OCAMLC) $(OCAMLFLAGS) -c $<

# %.cmo %.cmi: %.ml
# 	$(OCAMLC) $(OCAMLFLAGS) -c $<

# %.cmx %.cmi: %.ml
# 	$(OCAMLOPT) $(OCAMLOPTFLAGS) $<

# %.ml: %.mll
# 	$(OCAMLLEX) $<

# %.ml %.mli: %.mly
# 	$(MENHIR) $(MENHIRFLAGS) $<

# depend: .depend

# .depend: $(FILES)
# 	$(OCAMLDEP) $(FILES) > .depend
