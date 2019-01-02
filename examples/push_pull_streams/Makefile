ZELUC = ../../compiler/zeluc.byte
ZLIB=../../lib

main1: join.zls
	$(ZELUC) -s main1 join.zls
	ocamlc -I $(ZLIB) -o main1 join.ml main1.ml

main2: join.zls
	$(ZELUC) -s main2 join.zls
	ocamlc -I $(ZLIB) -o main2 join.ml main2.ml

main3: join.zls
	$(ZELUC) -s main3 join.zls
	ocamlc -I $(ZLIB) -o main3 join.ml main3.ml

clean:
	rm -f join.ml main1.ml main2.ml main3.ml
	rm -f main1 main2 main3
	rm -f join.zci
	rm -f *.cmi *.cmo *.cmxi *.cmxo

