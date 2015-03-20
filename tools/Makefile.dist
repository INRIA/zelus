include ./config

.PHONY: help install uninstall examples

help:
	@printf "Type 'make install' to install Zélus into:\n"
	@printf "    ${bindir}\n"
	@printf "    ${libdir}\n"
	@printf "\n"
	@printf "Type 'make examples' to build the examples.\n"

install:
	mkdir -p ${bindir}
	cp bin/zeluc.byte ${bindir}/
	cp bin/zeluc ${bindir}/
	mkdir -p ${libdir}
	cp lib/* ${libdir}/
	$(OCAMLFIND) install zelus META || true

uninstall:
	rm -f ${bindir}/zeluc.byte
	rm -f ${bindir}/zeluc
	rm -rf ${libdir}
	$(OCAMLFIND) remove zelus || true

examples:
	@for i in `ls examples`; do ${MAKE} -C examples/$$i byte; done;

