include config

default: $(targets) $(gtktargets)

all: depend
	(cd compiler; $(MAKE) -f Makefile all)
	(cd lib;      $(MAKE) -f Makefile all)
	(cd tools;    $(MAKE) -f Makefile all)

byte: depend
	(cd compiler; $(MAKE) -f Makefile byte)
	(cd lib;      $(MAKE) -f Makefile byte)
	(cd tools;    $(MAKE) -f Makefile all)

withgtk.byte: depend
	(cd compiler; $(MAKE) -f Makefile byte)
	(cd lib;      $(MAKE) -f Makefile withgtk.byte)
	(cd tools;    $(MAKE) -f Makefile all)

opt: depend
	(cd compiler; $(MAKE) -f Makefile opt)
	(cd lib;      $(MAKE) -f Makefile opt)
	(cd tools;    $(MAKE) -f Makefile all)

withgtk.opt: depend
	(cd compiler; $(MAKE) -f Makefile opt)
	(cd lib;      $(MAKE) -f Makefile withgtk.opt)
	(cd tools;    $(MAKE) -f Makefile all)

debug: depend debug.txt
	(cd compiler; $(MAKE) -f Makefile debug)
	(cd lib;      $(MAKE) -f Makefile debug)
	(cd tools;    $(MAKE) -f Makefile debug)

tests: all
	(cd test/good; $(MAKE) -f Makefile)
	(cd test/bad;  $(MAKE) -f Makefile)

depend:
	(cd compiler; $(MAKE) -f Makefile depend)
	(cd lib;      $(MAKE) -f Makefile depend)
	(cd tools;    $(MAKE) -f Makefile depend)

debug.txt:
	@printf "$$DEBUG_PRELUDE\n" > $@
	@printf "set arguments -I $(ZLLIB) <file-to-compile>\n\n" >> $@

loc:
	@(cd compiler; \
	  #printf "\\\\multirow{2}{l}{\\\\textbf{Compiler}}\\\\\n"; \
	  $(MAKE) --no-print-directory -f Makefile loc; \
	 cd ../lib; \
	  printf "\\\\multirow{2}{l}{\\\\textbf{Runtime}}\\\\\n"; \
	 $(MAKE) --no-print-directory -f Makefile loc) | \
	 	awk 'BEGIN { last="" } /^[^ ]/ { print last; printf("    %s ", $$0) } /^ / {last = sprintf("& %s \\\\", $$1)} END {print last}'

dist:
	$(MAKE) cleanall
	./configure --disable-opt --disable-sundials
	$(MAKE) all makedist
	$(MAKE) cleanall
	./configure --disable-opt
	$(MAKE) all makedist

makedist:
	@printf "$(S_BLUE)## Populating toplevel directory$(S_NORMAL)\n"
	rm -rf zelus-dist/
	mkdir -p zelus-dist/
	cp tools/Makefile.dist zelus-dist/Makefile
	sed -e 's/for_compile=.*/for_compile=0/' configure > zelus-dist/configure
	chmod ug+x zelus-dist/configure
	cp config.in zelus-dist/
	cp tools/readme.md.dist zelus-dist/readme.md
	cp license.*.txt zelus-dist/
	@#
	@printf "$(S_BLUE)## Populating lib subdirectory$(S_NORMAL)\n"
	mkdir -p zelus-dist/lib
	cp lib/zllib.cma lib/zllibgtk.cma zelus-dist/lib/
	#cp lib/zllib.cmxa lib/zllibgtk.cmxa zelus-dist/lib/
	cp lib/*.zli lib/*.zci zelus-dist/lib/
	cp lib/*.cmi zelus-dist/lib/
	@#
	@printf "$(S_BLUE)## Populating bin subdirectory$(S_NORMAL)\n"
	mkdir -p zelus-dist/bin
	@(read x; printf "#!/usr/bin/env ocamlrun\n"; cat) \
	    < compiler/zeluc.byte > zelus-dist/bin/zeluc.byte
	@chmod ugo+x zelus-dist/bin/zeluc.byte
	@#
	@printf "$(S_BLUE)## Populating examples subdirectory$(S_NORMAL)\n"
	mkdir -p zelus-dist/examples
	cp examples/Makefile zelus-dist/examples/
	-(cd examples; make DISTDIR=../../zelus-dist/examples export)
	@printf "$(S_BLUE)## Creating package$(S_NORMAL)\n"
	@#ARCH=`uname -s`-`uname -m`;
	@VERSIONSTR=`./compiler/zeluc.byte -version`;			\
	  VERSION=`expr "$${VERSIONSTR}" : '.*version \\(.*\\) (.*'`;	\
	  ARCH=byte;							\
	  DISTNAME="zelus-$${VERSION}$(DISTOPTION)-$${ARCH}";		\
	  rm -rf "$${DISTNAME}";					\
	  mv zelus-dist "$${DISTNAME}";					\
	  tar czvf "$${DISTNAME}.tar.gz" "$${DISTNAME}";		\
	  OCAMLVERSION=`$(OCAMLC) -version`;				\
	  ARCH=`uname -s`-`uname -m`;					\
	  printf "$(S_RED)## Compiled with OCaml $${OCAMLVERSION} ";	\
	  printf "and using the $(SOLVER) solver ($${DISTNAME}).$(S_NORMAL)\n"

install:
	@for target in $(targets); do case $$target in 		\
	  byte) cp compiler/$(BIN).byte $(bindir)/$(BIN);	\
	        printf "$(bindir)/$(BIN)  --$(S_RED)";		\
		head -n 1 compiler/$(BIN).byte;			\
		printf "$(S_NORMAL)";;				\
	  opt)  cp compiler/$(BIN).opt $(bindir)/$(BIN).opt;	\
	  	printf "$(bindir)/$(BIN).opt\n";;		\
	esac done
	@mkdir -p $(libdir)
	@printf "libdir: $(libdir)\n"
	@cp `ls lib/*.cma lib/*.cmxa lib/*.a lib/*.cmi lib/*.zci` $(libdir)/

uninstall:
	rm $(bindir)/$(BIN)
	rm $(libdir)/*.cma $(libdir)/*.cmxa $(libdir)/*.cmi
	rm $(libdir)/*.a $(libdir)/*.zci
	rmdir $(libdir)

opam-dist:
	mkdir -p opam-dist/zelus/
	@printf "$(S_BLUE)## Populating source directory$(S_NORMAL)\n"
	cp -r  compiler bin lib tools Makefile config.in configure license.*.txt opam-dist/zelus/
	#
	@printf "$(S_BLUE)## Creating package$(S_NORMAL)\n"
	(cd opam-dist; tar cvzf zelus.tar.gz zelus)
	#
	@printf "$(S_BLUE)## Removing source files$(S_NORMAL)\n"
	rm -rf opam-dist/zelus
	#
	@printf "$(S_BLUE)## Set path for the opam repository$(S_NORMAL)\n"
	(cd packages/zelus.0.6; sed -i '' "s#@path@#$(shell pwd)#" url)


opam-install:
	@printf "bin: [\"compiler/$(BIN).$(TARGET)\" {\"zeluc\"}]\n" >> zelus.install ; \
	printf "lib: [\n" >> zelus.install ; \
	for file in lib/*.cma lib/*.cmxa lib/*.a lib/*.cmi lib/*.zci ; do \
	      printf "  \"$$file\"\n" >> zelus.install ; \
	    done ; \
	 printf "]\n" >> zelus.install ; \

# Clean up
clean:
	(cd compiler;  make -f Makefile clean)
	(cd lib;       make -f Makefile clean)
	(cd tools;     make -f Makefile clean)
	(cd test/good; make -f Makefile clean)
	(cd test/bad;  make -f Makefile clean)
	(cd examples;  make -f Makefile clean)
	@rm -rf debug.txt

realclean cleanall distclean:
	(cd compiler;  make -f Makefile cleanall)
	(cd lib;       make -f Makefile cleanall)
	(cd tools;     make -f Makefile cleanall)
	(cd test/good; make -f Makefile cleanall)
	(cd test/bad;  make -f Makefile cleanall)
	(cd examples;  make -f Makefile cleanall)

