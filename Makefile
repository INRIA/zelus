all:
	dune build compiler lib

examples:
	dune build examples

install:
	opam pin -k path .

uninstall:
	opam pin remove zelus zelus-gtk

clean:
	dune clean

docker-build:
	docker build -t zelus -f zelus.docker .

docker-run:
	docker run -ti --rm zelus bash
