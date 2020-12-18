all:
	dune build

install:
	opam install .

docker-build:
	docker build -t zelus -f zelus.docker .

docker-run:
	docker run -ti --rm zelus bash