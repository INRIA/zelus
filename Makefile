all:
	dune build

clean:
	dune clean

docker-build:
	docker build -t zelus -f zelus.docker .

docker-run:
	docker run -ti --rm zelus bash


# Doc (for opam):
# opam pin -k path .              : install the current version of the compiler
#                                   as an opam package
# opam pin --help

# opam pin remove zelus zelus-gtk : removes the opam package
# opam install zelus zelus-gtk : install the (public) opam package
