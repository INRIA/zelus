all:
	dune build

clean:
	dune clean

wc:
	wc compiler/global/*.ml \
	compiler/typing/*.ml \
	compiler/main/*.ml \
	compiler/parsing/*.mll compiler/parsing/*.mly \
	zrun/*.ml
