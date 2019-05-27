include ../../../../config

ZELUC = ../../../../bin/zeluc
ZLLIB = ../../../../lib
ZLEXTRALIBS = $(ZLGTKLIBS)


test_utils = adc dampp thrust tgear morelli pdot
utils_deps = ../matrix.cmo ../utils.cmo mlutils.cmo

test_lut = lut
lut_deps = ../matrix.cmo

deps_aux = $(utils_deps) $(utils_deps:.cmo=.zci) \
$(lut_deps) $(lut_deps:.cmo=.zci)
# remove duplicates
deps = $(echo $(deps_aux) | tr ' ' '\n' | awk '!a[$$0]++')

utils_%.ml: $(utils_deps:.cmo=.zci) test_utils.zls
	$(ZELUC) -I ../ -gtk2 -s test_$(@:utils_%.ml=%) -o $(@:.ml=) test_utils.zls
utils_%.byte: INCLUDES=$(utils_deps:../%=%)
utils_%.byte: $(utils_deps) utils_%.ml
	$(OCAMLC) -o $@ \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) \
			-I ../ $(INCLUDES) \
			test_utils.ml $(@:.byte=.ml)

lut_%.ml: $(lut_deps:.cmo=.zci) test_lut.zls
	$(ZELUC) -I ../ -gtk2 -s test_$(@:lut_%.ml=%) -o $(@:.ml=) test_lut.zls
lut_%.byte: INCLUDES=$(lut_deps:../%=%)
lut_%.byte: $(lut_deps) lut_%.ml
	$(OCAMLC) -o $@ \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) \
			-I ../ $(INCLUDES) \
			test_lut.ml $(@:.byte=.ml)

mlutils.zci: mlutils.zli
mlutils.cmo: mlutils.ml
	$(OCAMLC) -c -o $@ $<

$(deps):
	$(MAKE) -C ../ $(@:../%=%)

clean:
	-@rm -rf test_lut.ml
	-@rm -rf test_utils.ml
	-@rm -rf *.zci *.cm[iox]

cleanall realclean: clean
	-@rm -rf *.byte
