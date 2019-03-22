include ../../config

ZELUCFLAGS += -nodeadcode

OCAMLFLAGS += -I ../../lib
OCAMLOPTFLAGS += -I ../../lib
ZLEXTRALIBS = $(ZLGTKLIBS)

# SRC = predicates.zls next.zls always.zls and.zls or.zls trigger.zls \
# 		  always_or.zls macros.zls
TEST = absence absence_timed minimum_duration maximum_duration \
			 bounded_recurrence bounded_response bounded_invariance

default: $(word 1, $(targets))
all:  $(targets)
# byte: $(SRC:.zls=.byte)
# opt: $(SRC:.zls=.opt)
byte: templates_byte
opt: templates_opt

templates: templates_byte
templates_byte: $(TEST:%=test_%.byte)
templates_opt: $(TEST:%=test_%.opt)

$(SRC:.zls=.byte):
	$(MAKE) $(@:.byte=.ml) $(@:.byte=_main.ml)
	$(OCAMLC) $(OCAMLFLAGS) -o $@ \
	    $(ZLSTDLIBS) $(ZLEXTRALIBS) $(INCLUDES) $(@:.byte=.ml) $(@:.byte=_main.ml)

$(SRC:.zls=.opt):
	$(MAKE) $(@:.opt=.ml) $(@:.opt=_main.ml)
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ \
	    $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) \
			$(INCLUDES:.cma=.cmxa) $(@:.opt=.ml) $(@:.opt=_main.ml)

$(SRC:.zls=_c.byte):
	$(MAKE) $(@:.byte=.ml) $(@:_c.byte=_main_c.ml)
	$(OCAMLC) $(OCAMLFLAGS) -o $@ \
	    $(ZLSTDLIBS) $(ZLEXTRALIBS) $(INCLUDES) $(@:_c.byte=.ml) $(@:_c.byte=_main_c.ml)

$(SRC:.zls=_c.opt):
	$(MAKE) $(@:.opt=.ml) $(@:_c.opt=_main_c.ml)
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ \
	    $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) \
			$(INCLUDES:.cma=.cmxa) $(@:_c.opt=.ml) $(@:_c.opt=_main_c.ml)

$(SRC:.zls=.ml):
	$(ZELUC) $(ZELUCFLAGS) $(ZELUCEXTRAFLAGS) -gtk2 -s main -o $(@:.ml=_main) $(@:.ml=.zls)

$(SRC:.zls=_main.ml):
	$(ZELUC) $(ZELUCFLAGS) $(ZELUCEXTRAFLAGS) -gtk2 -s main -o $(@:.ml=) $(@:_main.ml=.zls)

$(SRC:.zls=_c.ml):
	$(ZELUC) $(ZELUCFLAGS) $(ZELUCEXTRAFLAGS) -gtk2 -s main_c -o $(@:_c.ml=_main_c) $(@:_c.ml=.zls)

$(SRC:.zls=_main_c.ml):
	$(ZELUC) $(ZELUCFLAGS) $(ZELUCEXTRAFLAGS) -gtk2 -s main_c -o $(@:_c.ml=_main_c) $(@:_main_c.ml=.zls)

pattern_templates.ml: pattern_templates.zls
	$(ZELUC) $(ZELUCFLAGS) $(ZELUCEXTRAFLAGS) pattern_templates.zls

$(TEST:%=test_%.ml): pattern_templates.zls
	$(ZELUC) $(ZELUCFLAGS) $(ZELUCEXTRAFLAGS) -gtk2 -s $(@:%.ml=%) \
			pattern_templates.zls

$(TEST:%=test_%.byte):
	$(MAKE) pattern_templates.ml $(@:.byte=.ml)
	$(OCAMLC) $(OCAMLFLAGS) -o $@ \
	    $(ZLSTDLIBS) $(ZLEXTRALIBS) $(INCLUDES) \
			pattern_templates.ml $(@:.byte=.ml)

$(TEST:%=test_%.opt):
	$(MAKE) pattern_templates.ml $(@:.opt=.ml)
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ \
	    $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) \
			$(INCLUDES:.cma=.cmxa) pattern_templates.ml $(@:.opt=.ml)

test:
test_formula.byte: formula.ml
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $^
test_formula.opt: formula.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $^

clean:
	-@rm -f $(SRC:.zls=.ml) $(SRC:.zls=_main.ml)
	-@rm -f $(SRC:.zls=_c.ml) $(SRC:.zls=_main_c.ml)
	-@rm -f pattern_templates.ml pattern_templates_main.ml $(TEST:%=test_%.ml)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci

realclean cleanall: clean
	-@rm -f $(SRC:.zls=.byte) $(SRC:.zls=.opt)
	-@rm -f $(SRC:.zls=_c.byte) $(SRC:.zls=_c.opt)
	-@rm -f $(TEST:%=test_%.byte) $(TEST:%=test_%.opt)
	-@rm -f test_formula.byte test_formula.opt
