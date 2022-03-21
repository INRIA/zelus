all: ## Build the compiler and libraries
	dune build compiler lib

test: ## Launch the tests via dune
	dune runtest --force

examples: ## Build all the examples
	dune build examples

tools: ## Build the tools
	dune build tools

install: ## Install as an opam development package pinned to this directory
	opam pin -k path .

uninstall: ## Remove opam pin
	opam pin remove zelus zelus-gtk

clean: ## Clean the entire project
	dune clean

docker-build: ## Build the Docker image
	docker build -t zelus -f zelus.docker .

docker-run: ## Launch a terminal in the Docker image
	docker run -ti --rm zelus bash

help: ## Print this help
	@awk 'BEGIN {FS = ":.*##"; printf "Usage:\n"} /^[a-zA-Z_-]+:.*?##/ { printf "  make %-20s# %s\n", $$1, $$2 }' $(MAKEFILE_LIST)

.PHONY: test help

# Doc (for opam):
# opam pin -k path .              : install the current version of the compiler
#                                   as an opam package
# opam pin --help

# opam pin remove zelus zelus-gtk : removes the opam package
# opam install zelus zelus-gtk : install the (public) opam package
