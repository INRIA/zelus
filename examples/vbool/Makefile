advanced_heater.cmo: advanced_heater.ml
	ocamlbuild -pkg zelus.gtk advanced_heater.cmo

advanced_heater.ml advanced_heater.zci: advanced_heater.zls
	zeluc advanced_heater.zls

advanced_heater_main.ml: advanced_heater.zls
	zeluc -gtk2 -s main -o advanced_heater_main advanced_heater.zls

advanced_heater_main.byte: advanced_heater_main.ml
	ocamlbuild -pkg zelus.gtk advanced_heater_main.byte

spec_main.ml: spec.zls advanced_heater.zci
	zeluc -gtk2 -s main -o spec_main spec.zls

spec_main.byte: spec_main.ml
	ocamlbuild -pkg zelus.gtk spec_main.byte

clean:
	ocamlbuild -clean
	rm -rf advanced_heater.ml advanced_heater_main.ml
	rm -rf spec.ml spec_main.ml
	rm -rf *.zci *.cm[iox]

cleanall: clean
	rm -rf *.byte
