include ../../config

ZLEXTRALIBS = $(ZLGTKLIBS)

EXAMPLE=bangbang.zls

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

export: bangbang.byte
	mkdir $(DISTDIR)/bangbang
	cp bangbang.zls Makefile readme.md $(DISTDIR)/bangbang/
	cp bangbang.byte $(DISTDIR)/bangbang/
	mkdir $(DISTDIR)/bangbang/img
	cp img/*.png $(DISTDIR)/bangbang/img/

clean:
	-@rm -f $(EXAMPLE:.zls=.ml) $(EXAMPLE:.zls=_main.ml)
	-@rm -f spec_main.ml spec_plot.ml spec.ml
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci

realclean cleanall: clean
	-@rm -rf *.byte *.opt

spec: spec_byte spec_opt spec_plot_byte spec_plot_opt
spec_byte: clean byte spec.byte
spec_opt: clean opt spec.opt
spec_plot_byte: clean byte spec_plot.byte
spec_plot_opt: clean opt spec_plot.opt

spec_plot.ml: ZLEXTRALIBS += $(EXAMPLE:.zls=.cmo)
spec_plot.ml: ZELUCFLAGS += -gtk2

spec.byte: bangbang.cmo spec.cmo spec_main.ml
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) graphics.cma \
	    $^
spec.opt: bangbang.cmx spec.cmx spec_main.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) graphics.cmxa \
	    $^

spec_plot.byte: bangbang.cmo spec.cmo spec_plot.ml
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) graphics.cma \
	    $^
spec_plot.opt: bangbang.cmx spec.cmx spec_plot.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) graphics.cmxa \
	    $^

# Common rules
.SUFFIXES : .ml .zls

spec_%.ml: spec.zls
	$(ZELUC) $(ZELUCFLAGS) -o $(<:.zls=)_$(@:spec_%.ml=%) -s $(@:spec_%.ml=%) $<
spec.ml: spec.zls
	$(ZELUC) $(ZELUCFLAGS) -o $(<:.zls=)_main -s main $<
bangbang.ml: bangbang.zls
	$(ZELUC) $(ZELUCFLAGS) -gtk2 -o $(<:.zls=)_main -s main $<
