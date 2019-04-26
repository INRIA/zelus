%.native: 
	ocamlbuild -use-ocamlfind -pkgs owl '$@'

all: lqr.native

clean:
	rm -rf _build/ lqr.native
