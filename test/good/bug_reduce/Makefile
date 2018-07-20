OCAMLBUILD :=                               \
  ocamlbuild                                \
    -classic-display                        \
    -j 4                                    \
    -use-ocamlfind                          \

ZELUC = zeluc
ZELUCFLAGS = -gtk2

DEPS = aux.ml
TARGET = bug.byte

all: $(DEPS:.ml=.zci) $(DEPS) $(TARGET:.byte=_main.byte)
clean:
	rm -f *.ml *.zci *.byte
	rm -rf _build
remake: clean all

%_main.byte: %.zls
	$(ZELUC) $(ZELUCFLAGS) -s main $^
	mv main.ml $(@:.byte=.ml)
	$(OCAMLBUILD) $@

%.ml: %.zls
	$(ZELUC) $(ZELUCFLAGS) $^

%.zci: %.zli
	$(ZELUC) $(ZELUCFLAGS) $^
