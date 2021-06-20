include ../color

ALL := $(shell ls *.zlus)
NTESTS := $(shell ls *.zlus | wc -l)
HALFLINE = "------------------------------"

.PRECIOUS: %.ml %.translation %.camldebug

compilation: compilation-quiet
	@$(MAKE) -s summary
compilation-quiet: $(ALL:.zlus=.compilation)

translation: translation-quiet
	@$(MAKE) -s translation-summary
translation-quiet: $(ALL:.zlus=.translation)

translation-summary:
	@TRANSOK=`ls | grep '\.translation.ok$$' | wc -l`;	\
	printf "$(S_BLUE)translation:   $$TRANSOK / $(NTESTS) (`expr $$TRANSOK \\* 100 / $(NTESTS)`%%)$(S_NORMAL)\n"

summary: translation-summary
	@COMPILOK=`ls | grep '\.compilation.ok$$' | wc -l`;	\
	printf "$(S_BLUE)compilation:   $$COMPILOK / $(NTESTS) (`expr $$COMPILOK \\* 100 / $(NTESTS)`%%)$(S_NORMAL)\n"

showtests:
	@for f in $(ALL); do					\
	    printf -- "-----$(HALFLINE)$(HALFLINE)good/$$f\n";	\
	    cat $$f;						\
	    printf "\n";					\
	done

help:
	-@printf "make                    run all tests\n"
	-@printf "make t0001 t0004        run tests 1 and 4\n"
	-@printf "make t0004.debug        show debugging detail for test 4\n"
	-@printf "make ADDFLAGS=-noinit t0004.debug\n"
	-@printf "                        additional flags for zeluc\n"
	-@printf "make t0004.translation  run the first part of test 4\n"
	-@printf "make t0001 VERBOSE=1    run test 1 and show more detail\n"
	-@printf "make NOCOLOR=1          run tests without ANSI color commands\n"
	-@printf "make showtests		show the contents of all tests\n"

clean:
	-@rm -rf *.ml *.obc *.zci *.cmi *.cmo *.cmxi *.cmx *.o *.annot a.out
	-@rm -rf *.compilation *.compilation.ok *.translation *.translation.ok
	-@rm -rf *.camldebug

realclean cleanall: clean

##
FORCE:

%: %.compilation ;

%.debug: %.zlus %.camldebug FORCE
	@cat $(<:.zlus=.camldebug)
	@printf -- "----------------------------------------------------------------------------\n\n"
	@FLAGS="$(ZELUCFLAGS) $(ADDFLAGS) `sed -ne 's/(\*.*TEST\[\([^]]*\)\].*\*)/\1/p' $(<)`"\
	 ; printf "$(ZELUC) $${FLAGS} -v $< 2>&1\n";						    \
	 $(ZELUC) $${FLAGS}  -v $< 2>&1 || true
	@printf -- "----------------------------------------------------------------------------\n"
	@printf "Compiling with ocamlc. See below:\n"
	@printf -- "----------------------------------------------------------------------------\n"
	$(OCAMLC) $(OCAMLFLAGS) -c -I $(ZLLIB) $(INCLUDES) $(<:.zlus=.ml) 2>&1 || true

%.camldebug: %.zlus
	@printf "$$DEBUG_PRELUDE\n" > $@
	@FLAGS="$(ZELUCFLAGS) $(ADDFLAGS)	`sed -ne 's/(\*.*TEST\[\([^]]*\)\].*\*)/\1/p' $(<)`"\
	 ; printf "set arguments -I $(ZLLIB) $${FLAGS}" "../test/good/$<\n" >> $@
%.ml %.translation: %.zlus FORCE
	-@FLAGS="$(ADDFLAGS)				\
	    `sed -ne 's/(\*.*TEST\[\([^]]*\)\].*\*)/\1/p' $(<)`";	\
	$(ZELUC) $${FLAGS} $< 2>$(<:.zlus=.translation);			\
	if [ $$? -eq 0 ]; then						\
	    if [ `cat $(<:.zlus=.translation) | wc -l` -ne 0 ];		\
	    then WARN=" (with warnings)"; else WARN=""; fi;		\
	    printf -- "--good/$(<:.zlus=): $(S_GREEN)translation ok$(S_NORMAL)$(WARN)\n"; \
	    touch "$(<:.zlus=.translation.ok)";				\
	else					  			\
	    printf -- "--good/$(<:.zlus=): $(S_RED)translation fail$(S_NORMAL) (see $(<:.zlus=.translation))\n";	\
	    rm -f "$(<:.zlus=.translation.ok)";				\
	fi
ifdef VERBOSE
	-@cat $(<:.zlus=.translation)
endif

%.compilation: %.translation FORCE
	-@$(OCAMLC) $(OCAMLFLAGS) -c -I $(ZLLIB) $(INCLUDES)		\
	    $(<:.translation=.ml) 2>$(<:.translation=.compilation);					\
	if [ $$? -eq 0 ]; then						\
	    if [ `cat $(<:.translation=.compilation) | wc -l` -ne 0 ];		\
	    then WARN=" (with warnings)"; else WARN=""; fi;		\
	    printf -- "--good/$(<:.translation=): $(S_GREEN)compilation ok$(S_NORMAL)\n"; \
	    touch "$(<:.translation=.compilation.ok)";				\
	elif [ ! -e $< ]; then						\
	    printf -- "--good/$(<:.translation=): compilation not tested\n";	\
	    rm -f "$(<:.translation=.compilation.ok)";				\
	else					  			\
	    printf -- "--good/$(<:.translation=): $(S_RED)compilation fail$(S_NORMAL) (see $(<:.translation=.compilation))\n"; \
	    rm -f "$(<:.translation=.compilation.ok)";				\
	fi
ifdef VERBOSE
	-@cat $(<:.translation=.compilation)
endif

