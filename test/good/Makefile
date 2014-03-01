include ../../config

ALL := $(shell ls t*.zls)
NTESTS := $(shell ls t*.zls | wc -l)
HALFLINE = "------------------------------"

.PRECIOUS: %.ml %.translation %.camldebug

compilation: compilation-quiet
	@$(MAKE) -s summary
compilation-quiet: $(ALL:.zls=.compilation)

translation: translation-quiet
	@$(MAKE) -s translation-summary
translation-quiet: $(ALL:.zls=.translation)

translation-summary:
	@TRANSOK=`ls | grep '\.translation.ok$$' | wc -l`;	\
	echo "$(S_BLUE)translation:   $$TRANSOK / $(NTESTS)"	\
	  "(`expr $$TRANSOK \\* 100 / $(NTESTS)`%)$(S_NORMAL)"

summary: translation-summary
	@COMPILOK=`ls | grep '\.compilation.ok$$' | wc -l`;	\
	echo "$(S_BLUE)compilation:   $$COMPILOK / $(NTESTS)"	\
	  "(`expr $$COMPILOK \\* 100 / $(NTESTS)`%)$(S_NORMAL)"

showtests:
	@for f in $(ALL); do				\
	    echo "-----$(HALFLINE)$(HALFLINE)good/$$f";	\
	    cat $$f;					\
	    echo;					\
	done

help:
	-@echo "make                    run all tests"
	-@echo "make t0001 t0004        run tests 1 and 4"
	-@echo "make t0004.debug        show debugging detail for test 4"
	-@echo "make ADDFLAGS=-noinit t0004.debug"
	-@echo "                        additional flags for zeluc"
	-@echo "make t0004.translation  run the first part of test 4"
	-@echo "make t0001 VERBOSE=1    run test 1 and show more detail"
	-@echo "make NOCOLOR=1          run tests without ANSI color commands"
	-@echo "make showtests		show the contents of all tests"

clean:
	-@rm -rf *.ml *.obc *.zci *.cmi *.cmo *.cmxi *.cmx *.o *.annot a.out
	-@rm -rf *.compilation *.compilation.ok *.translation *.translation.ok
	-@rm -rf *.camldebug

realclean cleanall: clean

##
FORCE:

%: %.compilation ;

%.debug: %.zls %.camldebug FORCE
	@cat $(<:.zls=.camldebug)
	@echo "----------------------------------------------------------------------------"
	@echo
	@FLAGS="$(ZELUCFLAGS) $(ADDFLAGS) `sed -ne 's/(\*.*TEST\[\([^]]*\)\].*\*)/\1/p' $(<)`"\
	 ; echo "$(ZELUC) $${FLAGS} -v $< 2>&1";						    \
	 $(ZELUC) $${FLAGS}  -v $< 2>&1 || true
	@echo "----------------------------------------------------------------------------"
	@echo "Compiling with ocamlc. See below:"
	@echo "----------------------------------------------------------------------------"
	$(OCAMLC) $(OCAMLFLAGS) -c -I $(ZLLIB) $(INCLUDES) $(<:.zls=.ml) 2>&1 || true

%.camldebug: %.zls
	@echo "$$DEBUG_PRELUDE" > $@
	@FLAGS="$(ZELUCFLAGS) $(ADDFLAGS)	`sed -ne 's/(\*.*TEST\[\([^]]*\)\].*\*)/\1/p' $(<)`"\
	 ; echo "set arguments -I $(ZLLIB) $${FLAGS}" "../test/good/$<" >> $@
%.ml %.translation: %.zls FORCE
	-@FLAGS="$(ADDFLAGS)				\
	    `sed -ne 's/(\*.*TEST\[\([^]]*\)\].*\*)/\1/p' $(<)`";	\
	$(ZELUC) $${FLAGS} $< 2>$(<:.zls=.translation);			\
	if [ $$? -eq 0 ]; then						\
	    if [ `cat $(<:.zls=.translation) | wc -l` -ne 0 ];		\
	    then WARN=" (with warnings)"; else WARN=""; fi;		\
	    echo "--good/$(<:.zls=):"					\
	    	 "$(S_GREEN)translation ok$(S_NORMAL)$(WARN)";		\
	    touch "$(<:.zls=.translation.ok)";				\
	else					  			\
	    echo "--good/$(<:.zls=):"					\
		 "$(S_RED)translation fail$(S_NORMAL)"			\
		 "(see $(<:.zls=.translation))";				\
	    rm -f "$(<:.zls=.translation.ok)";				\
	fi
ifdef VERBOSE
	-@cat $(<:.zls=.translation)
endif

%.compilation: %.ml FORCE
	-@$(OCAMLC) $(OCAMLFLAGS) -c -I $(ZLLIB) $(INCLUDES)		\
	    $< 2>$(<:.ml=.compilation);					\
	if [ $$? -eq 0 ]; then						\
	    if [ `cat $(<:.ml=.compilation) | wc -l` -ne 0 ];		\
	    then WARN=" (with warnings)"; else WARN=""; fi;		\
	    echo "--good/$(<:.ml=):"					\
	    	 "$(S_GREEN)compilation ok$(S_NORMAL)";			\
	    touch "$(<:.ml=.compilation.ok)";				\
	elif [ ! -e $< ]; then						\
	    echo "--good/$(<:.ml=):"					\
	    	 "compilation not tested";				\
	    rm -f "$(<:.ml=.compilation.ok)";				\
	else					  			\
	    echo "--good/$(<:.ml=):"					\
		 "$(S_RED)compilation fail$(S_NORMAL)"			\
		 "(see $(<:.ml=.compilation))";				\
	    rm -f "$(<:.ml=.compilation.ok)";				\
	fi
ifdef VERBOSE
	-@cat $(<:.ml=.compilation)
endif

