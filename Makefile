include config

default: $(targets) $(gtktargets)

all: depend
	(cd compiler; $(MAKE) -f Makefile all)
	(cd lib;      $(MAKE) -f Makefile all)
	(cd tools;    $(MAKE) -f Makefile all)

byte: depend
	(cd compiler; $(MAKE) -f Makefile byte)
	(cd lib;      $(MAKE) -f Makefile byte)

withgtk.byte: depend
	(cd compiler; $(MAKE) -f Makefile byte)
	(cd lib;      $(MAKE) -f Makefile withgtk.byte)

opt: depend
	(cd compiler; $(MAKE) -f Makefile opt)
	(cd lib;      $(MAKE) -f Makefile opt)

withgtk.opt: depend
	(cd compiler; $(MAKE) -f Makefile opt)
	(cd lib;      $(MAKE) -f Makefile withgtk.opt)

debug: depend debug.txt
	(cd compiler; $(MAKE) -f Makefile debug)
	(cd lib;      $(MAKE) -f Makefile debug)

tests: all
	(cd test/good; $(MAKE) -f Makefile)
	(cd test/bad;  $(MAKE) -f Makefile)

depend:
	(cd compiler; $(MAKE) -f Makefile depend)
	(cd lib;      $(MAKE) -f Makefile depend)

debug.txt:
	@echo "$$DEBUG_PRELUDE" > $@
	@echo "set arguments -I $(ZLLIB) <file-to-compile>" >> $@
	@echo "" >> $@

loc:
	@(cd compiler; \
	  echo "\\\\multirow{2}{l}{\\\\textbf{Compiler}}\\\\"; \
	  $(MAKE) --no-print-directory -f Makefile loc; \
	 cd ../lib; \
	  echo "\\\\multirow{2}{l}{\\\\textbf{Runtime}}\\\\"; \
	 $(MAKE) --no-print-directory -f Makefile loc) | \
	 	awk 'BEGIN { last="" } /^[^ ]/ { print last; printf("    %s ", $$0) } /^ / {last = sprintf("& %s \\\\", $$1)} END {print last}'

dist: all
	if [ ! -f sundialsml/config ]; \
	    then echo "$(S_RED)sundialsml is not configured!$(S_NORMAL)"; exit 1; fi
	#
	mkdir -p zelus-dist/
	@echo "$(S_BLUE)## Populating toplevel directory$(S_NORMAL)"
	cp tools/Makefile.dist zelus-dist/Makefile
	sed -e 's/for_compile=.*/for_compile=0/' configure > zelus-dist/configure
	chmod ug+x zelus-dist/configure
	cp config.in zelus-dist/
	cp tools/readme.md.dist zelus-dist/readme.md
	cp license.*.txt zelus-dist/
	#
	@echo "$(S_BLUE)## Populating lib-nosundials subdirectory$(S_NORMAL)"
	$(MAKE) -C lib cleanall
	$(MAKE) -C lib SOLVER=ode23 OPTIONAL_SOLVER_OBJS=""
	mkdir -p zelus-dist/lib-nosundials
	cp lib/zllib.cma lib/zllibgtk.cma zelus-dist/lib-nosundials/
	cp lib/loadsolvers.cmi zelus-dist/lib-nosundials/
	#
	@echo "$(S_BLUE)## Populating lib subdirectory$(S_NORMAL)"
	$(MAKE) -C lib cleanall
	$(MAKE) -C lib
	mkdir -p zelus-dist/lib
	cp lib/zllib.cma lib/zllibgtk.cma zelus-dist/lib/
	#cp lib/zllib.cmxa lib/zllibgtk.cmxa zelus-dist/lib/
	cp lib/*.lsi lib/*.lci zelus-dist/lib/
	cp lib/*.cmi zelus-dist/lib/
	#
	@echo "$(S_BLUE)## Populating sundialsml$(S_NORMAL)"
	mkdir -p zelus-dist/sundialsml
	make -C sundialsml PKGDIR=../zelus-dist/sundialsml/ \
	    		   STUBDIR=../zelus-dist/sundialsml/ \
			   INSTALL_DOCS=0 install
	cp sundialsml/sundials_license zelus-dist/sundialsml
	if [ `uname` = 'Darwin' ]; then \
	    LIBS=`otool -L sundialsml/dllmlsundials_cvode.so | grep libsundials | cut -d ' ' -f 1`; \
	  else \
	    LIBS=`ldd sundialsml/dllmlsundials_cvode.so | grep libsundials | cut -d ' ' -f 3`; \
	  fi; \
	  for f in $${LIBS}; do cp $$f zelus-dist/sundialsml/; \
	  			chmod ug+x zelus-dist/sundialsml/`basename $$f`; \
	  done
	#
	@echo "$(S_BLUE)## Populating bin subdirectory$(S_NORMAL)"
	mkdir -p zelus-dist/bin
	cp bin/zeluc.in zelus-dist/bin
	cp compiler/zeluc.byte zelus-dist/bin
	chmod a-x zelus-dist/bin/zeluc.byte
	#
	@echo "$(S_BLUE)## Populating examples subdirectory$(S_NORMAL)"
	mkdir -p zelus-dist/examples
	cp examples/Makefile zelus-dist/examples/
	-(cd examples; make DISTDIR=../../zelus-dist/examples export)
	@echo "$(S_BLUE)## Making bytecode distribution$(S_NORMAL)"
	cp -r zelus-dist zelus-byte
	rm -rf zelus-byte/sundialsml
	mv zelus-byte/lib-nosundials/* zelus-byte/lib
	rmdir zelus-byte/lib-nosundials
	@echo "$(S_BLUE)## Creating packages$(S_NORMAL)"
	VERSIONSTR=`./compiler/zeluc.byte -version`; \
	  VERSION=`expr "$${VERSIONSTR}" : '.*version \\(.*\\) (.*'`; \
	  ARCH=`uname -s`-`uname -m`; \
	  rm -rf "zelus-$${VERSION}-$${ARCH}"; \
	  mv zelus-byte "zelus-$${VERSION}.bytecode"; \
	  tar czvf "zelus-$${VERSION}.bytecode.tar.gz" "zelus-$${VERSION}.bytecode"; \
	  mv zelus-dist "zelus-$${VERSION}.$${ARCH}"; \
	  tar czvf "zelus-$${VERSION}.$${ARCH}.tar.gz" "zelus-$${VERSION}.$${ARCH}"
	#
	OCAMLVERSION=`$(OCAMLC) -version`; \
	ARCH=`uname -s`-`uname -m`; \
	  echo "$(S_RED)Compiled with OCaml $${OCAMLVERSION} for $${ARCH}$(S_NORMAL)"

opam-dist:
	mkdir -p opam-dist/zelus/
	@echo "$(S_BLUE)## Populating source directory$(S_NORMAL)"
	cp -r  compiler bin lib tools Makefile config.in configure license.*.txt opam-dist/zelus/
	#
	@echo "$(S_BLUE)## Creating package$(S_NORMAL)"
	(cd opam-dist; tar cvzf zelus.tar.gz zelus)
	#
	@echo "$(S_BLUE)## Removing source files$(S_NORMAL)"
	rm -rf opam-dist/zelus
	#
	@echo "$(S_BLUE)## Set path for the opam repository$(S_NORMAL)"
	(cd packages/zelus.0.6; sed -i '' "s#@path@#$(shell pwd)#" url)


opam-install:
	@echo "bin: [\"compiler/$(BIN).$(TARGET)\" {\"zeluc\"}]" >> zelus.install ; \
	echo "lib: [" >> zelus.install ; \
	for file in lib/*.cma lib/*.cmxa lib/*.a lib/*.cmi lib/*.lci ; do \
	      echo "  \"$$file\"" >> zelus.install ; \
	    done ; \
	 echo "]" >> zelus.install ; \

# Clean up
clean:
	(cd compiler;  make -f Makefile clean)
	(cd lib;       make -f Makefile clean)
	(cd test/good; make -f Makefile clean)
	(cd test/bad;  make -f Makefile clean)
	(cd examples;  make -f Makefile clean)
	@rm -rf debug.txt

realclean cleanall:
	(cd compiler;  make -f Makefile cleanall)
	(cd lib;       make -f Makefile cleanall)
	(cd test/good; make -f Makefile cleanall)
	(cd test/bad;  make -f Makefile cleanall)
	(cd examples;  make -f Makefile cleanall)

