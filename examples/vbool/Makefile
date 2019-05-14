advanced_heater.cmo: advanced_heater.ml
	ocamlbuild -r -pkg zelus.gtk advanced_heater.cmo

advanced_heater.ml advanced_heater.zci: advanced_heater.zls
	zeluc advanced_heater.zls

advanced_heater_main.ml: advanced_heater.zls
	zeluc -gtk2 -s main -o advanced_heater_main advanced_heater.zls

advanced_heater_main.byte: advanced_heater_main.ml
	ocamlbuild -r -pkg zelus.gtk advanced_heater_main.byte

spec_main.ml: spec.zls advanced_heater.zci input.zci zlutils.zci
	zeluc -gtk2 -s main -o spec_main spec.zls

spec_main.byte: spec_main.ml input.cmo zlutils.cmo
	ocamlbuild -r -pkg zelus.gtk spec_main.byte

list.zci: list.zli
	zeluc list.zli

zlutils.zci: zlutils.zli
	zeluc zlutils.zli

zlutils.cmo: zlutils.ml
	ocamlbuild -pkg zelus.gtk zlutils.cmo

input.ml input.zci: input.zls list.zci zlutils.zci
	zeluc input.zls

input.cmo: input.ml
	ocamlbuild -pkg zelus.gtk input.cmo

input_main.ml: input.zls list.zci zlutils.zci
	zeluc -gtk2 -s main -o input_main input.zls

input_main.byte: input_main.ml
	ocamlbuild -pkg zelus.gtk input_main.byte

clean:
	ocamlbuild -clean
	rm -rf advanced_heater.ml advanced_heater_main.ml
	rm -rf spec.ml spec_main.ml
	rm -rf input.ml input_main.ml
	rm -rf *.zci *.cm[iox]

cleanall: clean
	rm -rf *.byte
