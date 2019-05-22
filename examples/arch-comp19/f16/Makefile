include ../../../config

ZELUC = ../../../bin/zeluc
ZLLIB = ../../../lib

%.ml %.zci: %.zls
	$(ZELUC) $<
%.cmo:%.ml

# dependencies

utils.ml: matrix.zci
utils.cmo: matrix.cmo

subf16_model.ml: types.zci utils.zci
subf16_model.cmo: types.cmo utils.cmo

gcasAutopilot.ml: utils.zci types.zci
gcasAutopilot.cmo: utils.cmo types.cmo

controlledf16.ml: types.zci gcasAutopilot.zci lowLevelController.zci subf16_model.zci
controlledf16.cmo: types.cmo gcasAutopilot.cmo lowLevelController.cmo subf16_model.cmo

clean:
	-@rm -rf types.ml
	-@rm -rf lowLevelController.ml
	-@rm -rf gcasAutopilot.ml
	-@rm -rf controlledf16.ml
	-@rm -rf subf16_model.ml
	-@rm -rf utils.ml
	-@rm -rf *.annot *.zci *.cm[iox]

cleanall realclean: clean
	-@rm -rf *.byte *.opt *.out
