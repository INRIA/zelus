all:
	dune build

docker-build:
	docker build -t zelus -f zelus.docker .

docker-run:
	docker run -ti --rm zelus bash