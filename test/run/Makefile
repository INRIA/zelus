include ../color

ALL := $(shell ls *.zlus)
NTESTS := $(shell ls *.zlus | wc -l)
HALFLINE = "------------------------------"

.PRECIOUS: %.ml %_main.ml %.translation %.test %.camldebug

run: run-quiet
	@$(MAKE) -s summary
run-quiet: $(ALL:.zlus=)

summary:
	@TESTOK=`ls | grep '\\.ok$$' | wc -l`;			\
	printf "$(S_BLUE)valid runs:    $$TESTOK / $(NTESTS) (`expr $$TESTOK \\* 100 / $(NTESTS)`%%)$(S_NORMAL)\n"

showtests:
	@for f in $(ALL); do					\
	    printf -- "-----$(HALFLINE)$(HALFLINE)-run/$$f\n";	\
	    cat $$f;						\
	    printf "\n";					\
	done

help:
	-@printf "make                    run all tests\n"
	-@printf "make t0001 t0004        run tests 1 and 4\n"
	-@printf "make t0004.debug        show debugging detail for test 4\n"
	-@printf "make ADDFLAGS=-noinit t0004.debug\n"
	-@printf "                        additional flags for zeluc\n"
	-@printf "make t0001 VERBOSE=1    run test 1 and show more detail\n"
	-@printf "make NOCOLOR=1          run tests without ANSI color commands\n"

clean:
	-@rm -rf *.ml *.obc *.zci *.cmi *.cmo *.cmxi *.cmx *.o *.annot a.out
	-@rm -rf *.translation *.compilation *.ok *.test *.log *.camldebug

realclean cleanall: clean

##
FORCE:

%.debug: %.zlus %.camldebug
	@cat $(<:.zlus=.camldebug)
	@printf -- "----------------------------------------------------------------------------\n\n"
	@FLAGS="$(ZELUCFLAGS) $(ADDFLAGS) -s main					\
	    `sed -ne 's/(\*.*TEST\[\([^]]*\)\].*\*)/\1/p' $(<)`";	\
	$(ZELUC) $${FLAGS} -v $< 2>&1 || true

%.camldebug: %.zlus
	@printf "$$DEBUG_PRELUDE\n" > $@
	@printf "set arguments -I $(ZLLIB) $(ZELUCFLAGS)" "../test/run/$<\n" >> $@

%.ml %_main.ml %.translation: %.zlus FORCE
	-@FLAGS="$(ZELUCFLAGS) $(ADDFLAGS) -s main			\
	    `sed -ne 's/(\*.*TEST\[\([^]]*\)\].*\*)/\1/p' $(<)`";	\
	$(ZELUC) $${FLAGS} $< 2>$(<:.zlus=.translation);			\
	RESULT=$$?;							\
	if [ $(VERBOSE) ]; then printf "$(ZELUC) $${FLAGS} $<\n"; fi;	\
	if [ $${RESULT} -ne 0 ]; then					\
	    printf -- "-- run/$(<:.zlus=): $(S_RED)translation fail$(S_NORMAL) (see $(<:.zlus=.translation))\n"; \
	    rm -f "$(<:.zlus=.ok)" "$(<:.zlus=.test)";			\
	    rm -f $(<:%.zlus=%)_main.ml;					\
	else								\
	    mv main.ml $(<:%.zlus=%)_main.ml;				\
	fi
ifdef VERBOSE
	-@cat $(<:.zlus=.translation)
endif

%.test %.compilation: %.ml %_main.ml FORCE
	-@ARGS="$(OCAMLFLAGS) -o $(<:.ml=.test) $(INCLUDES)		\
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS)			\
	    $< $(<:.ml=_main.ml)";					\
	$(OCAMLC) $${ARGS} 2>$(<:.ml=.compilation);			\
	RESULT=$$?;							\
	if [ $(VERBOSE) ]; then printf "$(OCAMLC) $${ARGS}\n"; fi;	\
	if [ -e "$(<:.ml=_main.ml)" -a $${RESULT} -ne 0 ]; then		\
	    printf -- "-- run/$(<:.ml=): $(S_RED)compilation fail$(S_NORMAL) (see $(<:.ml=.compilation))\n"; \
	    rm -f "$(<:.ml=.ok)" "$(<:.ml=.test)";			\
	fi
ifdef VERBOSE
	-@cat $(<:.ml=.compilation)
endif

%: %.test FORCE
	-@ARGS="-fullspeed -l `sed -ne 's/(\*.*ARGS\[\([^]]*\)\].*\*)/\1/p' $(<:.test=.zlus)`";\
	if [ $(VERBOSE) ]; then echo "$(<) $${ARGS}"; fi;		\
	./$(<) $${ARGS} > $(<:.test=.log) 2>&1;				\
	RESULT=$$?;							\
	if [ $(VERBOSE) ]; then printf "$(<) $${ARGS}\n"; fi;		\
	if [ $${RESULT} -eq 0 ]; then					\
	    printf -- "-- run/$(<:.test=): $(S_GREEN)ok$(S_NORMAL)\n";	\
	    touch $(<:.test=.ok);					\
	elif [ -e $< ]; then						\
	    printf -- "-- run/$(<:.test=): $(S_RED)fail$(S_NORMAL) (see $(<:.test=.log))\n"; \
	    rm -f "$(<:.test=.ok)";					\
	fi
ifdef VERBOSE
	-@cat $(<:.test=.log)
endif

