include ../../../config

ZELUC = ../../../bin/zeluc
ZLLIB = ../../../lib

%.ml %.zci: %.zls
	$(ZELUC) $(ZLFLAGS) $<
%.cmo:%.ml

%.byte: ZLEXTRALIBS=$(ZLGTKLIBS)
%.byte: %.ml
	$(OCAMLC) $(OCAMLFLAGS) -o $@ \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) \
			$(INCLUDES) \
	    $< $(<:.ml=_main.ml)
%.opt: ZLEXTRALIBS=$(ZLGTKLIBS)
%.opt: %.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ \
	    -I $(ZLLIB) $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) \
			$(INCLUDES) \
	    $< $(<:.ml=_main.ml)

%_main.ml: %.zls
	$(ZELUC) -s main -gtk2 -o $(@:.ml=) $<

# dependencies

utilsDeps = matrix.cmo
utils.ml: $(utilsDeps:.cmo=.zci)
utils.cmo: $(utilsDeps)

subf16_modelDeps = types.cmo utils.cmo
subf16_model.ml: $(subf16_modelDeps:.cmo=.zci)
subf16_model.cmo: $(subf16_modelDeps)

lowLevelControllerDeps = types.cmo matrix.cmo utils.cmo
lowLevelController.ml: $(lowLevelControllerDeps:.cmo=.zci)
lowLevelController.cmo: $(lowLevelControllerDeps)

gcasAutopilotDeps = utils.cmo types.cmo
gcasAutopilot.ml: $(gcasAutopilotDeps:.cmo=.zci)
gcasAutopilot.cmo: $(gcasAutopilotDeps)

controlledf16Deps = types.cmo gcasAutopilot.cmo lowLevelController.cmo \
							      subf16_model.cmo
controlledf16.ml: $(controlledf16Deps:.cmo=.zci)
controlledf16.cmo: $(controlledf16Deps)

run_controlledf16Deps = types.cmo matrix.cmo utils.cmo gcasAutopilot.cmo \
											 lowLevelController.cmo subf16_model.cmo \
											 controlledf16.cmo
run_controlledf16.ml run_controlledf16_main.ml: $(run_controlledf16Deps:.cmo=.zci)
run_controlledf16.cmo: $(run_controlledf16Deps)
run_controlledf16.byte: INCLUDES += $(run_controlledf16Deps)
run_controlledf16.byte: $(run_controlledf16Deps) run_controlledf16_main.ml

run_subf16_modelDeps = types.cmo matrix.cmo utils.cmo subf16_model.cmo
run_subf16_model.ml run_subf16_model_main.ml: $(run_subf16_modelDeps:.cmo=.zci)
run_subf16_model.cmo: $(run_subf16_modelDeps)
run_subf16_model.byte: INCLUDES += $(run_subf16_modelDeps)
run_subf16_model.byte: $(run_subf16_modelDeps) run_subf16_model_main.ml

clean:
	$(MAKE) -C test clean
	-@rm -rf types.ml
	-@rm -rf lowLevelController.ml
	-@rm -rf gcasAutopilot.ml
	-@rm -rf controlledf16.ml
	-@rm -rf subf16_model.ml
	-@rm -rf run_subf16_model.ml run_subf16_model_main.ml
	-@rm -rf run_controlledf16.ml run_controlledf16_main.ml
	-@rm -rf utils.ml
	-@rm -rf *.annot *.zci *.cm[iox]

cleanall realclean: clean
	$(MAKE) -C test cleanall
	-@rm -rf *.byte *.opt *.out
