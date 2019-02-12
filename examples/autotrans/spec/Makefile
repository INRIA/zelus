include ../../../config

ZELUC = ../../../bin/zeluc

OBSERVERS = phi1_d phi2_d phi3_d phi4_d phi5_d phi6_d phi7_d phi8_d
REFERENCE = phi1_ref phi2_ref phi3_ref phi4_ref phi5_ref phi6_ref phi7_ref phi8_ref

ZELUCFLAGS += -I ../../../lib -I ../
OCAMLFLAGS += -I ../../../lib -I ../
INCLUDES += specutils.cmo # mlutils.cmo obsdutils.cmo obsd.cmo

ZLEXTRALIBS = $(ZLGTKLIBS)

AUTOTRANSINCL = ../maneuvers.cmo ../utils.cmo ../consts.cmo ../common.cmo \
								../autotransc.cmo ../autotransd.cmo

all: observers reference

observers: plot_observers cli_observers
reference: plot_reference cli_reference

plot_reference: $(REFERENCE:=.plot)
cli_reference: $(REFERENCE:=.cli)

plot_observers: $(OBSERVERS:=.plot)
cli_observers: $(OBSERVERS:=.cli)

plot: plot_reference plot_observers
cli: cli_reference cli_observers

$(REFERENCE) $(OBSERVERS):
	$(MAKE) $(@:=.plot) $(@:=.cli)

$(AUTOTRANSINCL):
	$(MAKE) -C ../

remake_%:
	@rm -f $(@:remake_%=%.plot) $(@:remake_%=%.cli)
	@rm -f $(@:remake_%=%_plot.ml)    $(@:remake_%=%_cli.ml)
	@rm -f $(@:remake_%=%_plot.cmi)   $(@:remake_%=%_cli.cmi)
	@rm -f $(@:remake_%=%_plot.cmo)   $(@:remake_%=%_cli.cmo)
	@rm -f $(@:remake_%=%_plot.zci)   $(@:remake_%=%_cli.zci)
	@rm -f $(@:remake_%=%_plot.annot) $(@:remake_%=%_cli.annot)
	$(MAKE) $(@:remake_%=%.plot) $(@:remake_%=%.cli)

%.plot: ZELUCFLAGS += -gtk2
%.plot: $(AUTOTRANSINCL) spec.cmo
	$(MAKE) \
		ZELUCFLAGS='$(ZELUCFLAGS)' \
		OCAMLFLAGS='$(OCAMLFLAGS)' \
		ZLEXTRALIBS='$(ZLEXTRALIBS)' \
		INCLUDES='$(INCLUDES)' \
		$(@:.plot=_plot.ml)
	$(OCAMLC) $(OCAMLFLAGS) -o $@ \
	   $(ZLSTDLIBS) $(ZLEXTRALIBS) \
		 $(INCLUDES) $^ $(@:.plot=.ml) $(@:.plot=_plot.ml)

%.cli: $(AUTOTRANSINCL) spec.cmo
	$(MAKE) \
		ZELUCFLAGS='$(ZELUCFLAGS)' \
		OCAMLFLAGS='$(OCAMLFLAGS)' \
		ZLEXTRALIBS='$(ZLEXTRALIBS)' \
		INCLUDES='$(INCLUDES)' \
		$(@:.cli=_cli.ml)
	$(OCAMLC) $(OCAMLFLAGS) -o $@ \
	   $(ZLSTDLIBS) $(ZLEXTRALIBS) \
		 $(INCLUDES) $^ $(@:.cli=.ml) $(@:.cli=_cli.ml)

%_cli.ml: %.zls
	$(ZELUC) $(ZELUCFLAGS) $(ZELUCEXTRAFLAGS) -s cli -o $(@:.ml=) \
		$(@:_cli.ml=.zls)

%_plot.ml: %.zls
	$(ZELUC) $(ZELUCFLAGS) $(ZELUCEXTRAFLAGS) -s plot -o $(@:.ml=) \
		$(@:_plot.ml=.zls)

check: TESTS = $(shell find . -name '*.cli')
check: cli
	$(MAKE) $(TESTS:./%=%.run)

%.run:
	@echo
	@echo ./$(@:.run=) -fullspeed -maxt 30
	@printf "> "
	@TEST=$$(./$(@:.run=) -fullspeed -maxt 30) || EXIT_CODE=$$? && true; \
	if [ -z "$$TEST" -a -z "$$EXIT_CODE" ]; then echo "OK."; else echo $$TEST; fi
	@echo

crosscheck: $(OBSERVERS:_d=.crosscheck)

%.crosscheck: %_d.cli %_ref.cli
	./$(@:.crosscheck=_d.cli) || true
	@echo
	./$(@:.crosscheck=_ref.cli) || true
	@echo
	@echo


clean:
	@rm -rf $(OBSERVERS:=.ml)    $(OBSERVERS:=_plot.ml)    $(OBSERVERS:=_cli.ml)
	@rm -rf $(OBSERVERS:=.cmi)   $(OBSERVERS:=_plot.cmi)   $(OBSERVERS:=_cli.cmi)
	@rm -rf $(OBSERVERS:=.cmo)   $(OBSERVERS:=_plot.cmo)   $(OBSERVERS:=_cli.cmo)
	@rm -rf $(OBSERVERS:=.zci)   $(OBSERVERS:=_plot.zci)   $(OBSERVERS:=_cli.zci)
	@rm -rf $(OBSERVERS:=.annot) $(OBSERVERS:=_plot.annot) $(OBSERVERS:=_cli.annot)
	@rm -rf $(REFERENCE:=.zci)   $(REFERENCE:=_plot.zci)   $(REFERENCE:=_cli.zci)
	@rm -rf $(REFERENCE:=.ml)    $(REFERENCE:=_plot.ml)    $(REFERENCE:=_cli.ml)
	@rm -rf $(REFERENCE:=.cmi)   $(REFERENCE:=_plot.cmi)   $(REFERENCE:=_cli.cmi)
	@rm -rf $(REFERENCE:=.cmo)   $(REFERENCE:=_plot.cmo)   $(REFERENCE:=_cli.cmo)
	@rm -rf $(REFERENCE:=.annot) $(REFERENCE:=_plot.annot) $(REFERENCE:=_cli.annot)
	@rm -rf spec.ml spec.cmi spec.cmo spec.zci spec.annot
	@rm -rf specutils.cmi specutils.cmo specutils.zci specutils.annot

realclean cleanall: clean
	@rm -rf $(OBSERVERS) $(OBSERVERS:=.plot) $(OBSERVERS:=.cli)
	@rm -rf $(REFERENCE) $(REFERENCE:=.plot) $(REFERENCE:=.cli)

#####  DEPS

spec.ml: specutils.zci
spec.cmo: specutils.cmo

##### COMMON

%.zci %.ml: %.zls
	$(ZELUC) $(ZELUCFLAGS) $<
