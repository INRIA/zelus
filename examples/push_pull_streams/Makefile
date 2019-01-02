main1: join.zls
	zeluc -s main1 join.zls
	ocamlc -I `zeluc -where` -o main1 join.ml main1.ml

main2: join.zls
	zeluc -s main2 join.zls
	ocamlc -I `zeluc -where` -o main2 join.ml main2.ml

main3: join.zls
	zeluc -s main3 join.zls
	ocamlc -I `zeluc -where` -o main3 join.ml main3.ml

clean:
	rm -f join.ml main1.ml main2.ml main3.ml
	rm -f main1 main2 main3
	rm -f join.zci
	rm -f *.cmi *.cmo *.cmxi *.cmxo

