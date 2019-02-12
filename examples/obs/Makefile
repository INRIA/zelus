include ../../config

OCAMLFLAGS += -I ../../lib
OCAMLOPTFLAGS += -I ../../lib
ZLEXTRALIBS = $(ZLGTKLIBS)

SRC = predicates.zls next.zls always.zls and.zls or.zls trigger.zls always_or.zls

default: $(word 1, $(targets))
all:  $(targets)
byte: $(SRC:.zls=.byte)
opt: $(SRC:.zls=.opt)

$(SRC:.zls=.byte):
	$(MAKE) $(@:.byte=.ml) $(@:.byte=_main.ml)
	$(OCAMLC) $(OCAMLFLAGS) -o $@ \
	    $(ZLSTDLIBS) $(ZLEXTRALIBS) $(INCLUDES) $(@:.byte=.ml) $(@:.byte=_main.ml)

$(SRC:.zls=.ml):
	$(ZELUC) $(ZELUCFLAGS) $(ZELUCEXTRAFLAGS) -gtk2 -s main -o $(@:.ml=_main) $(@:.ml=.zls)

clean:
	@rm -f $(SRC:.zls=.zci) $(SRC:.zls=.ml) $(SRC:.zls=_main.ml)
	@rm -f $(SRC:.zls=.byte) $(SRC:.zls=.opt)
	@rm -f $(SRC:.zls=.cmo) $(SRC:.zls=.cmx) $(SRC:.zls=.cmi) $(SRC:.zls=.annot)
	@rm -f $(SRC:.zls=_main.cmo) $(SRC:.zls=_main.cmx) $(SRC:.zls=_main.cmi) $(SRC:.zls=_main.annot)
