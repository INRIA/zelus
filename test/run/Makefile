include ../../config

ALL := $(shell ls t*.ls)
NTESTS := $(shell ls t*.ls | wc -l)
HALFLINE = "------------------------------"

.PRECIOUS: %.ml %_main.ml %.translation %.test %.camldebug

run: run-quiet
	@$(MAKE) -s summary
run-quiet: $(ALL:.ls=)

summary:
	@TESTOK=`ls | grep '\\.ok$$' | wc -l`;			\
	echo "$(S_BLUE)valid runs:    $$TESTOK / $(NTESTS)"	\
	  "(`expr $$TESTOK \\* 100 / $(NTESTS)`%)$(S_NORMAL)"

showtests:
	@for f in $(ALL); do				\
	    echo "-----$(HALFLINE)$(HALFLINE)-run/$$f";	\
	    cat $$f;					\
	    echo;					\
	done

help:
	-@echo "make                    run all tests"
	-@echo "make t0001 t0004        run tests 1 and 4"
	-@echo "make t0004.debug        show debugging detail for test 4"
	-@echo "make ADDFLAGS=-noinit t0004.debug"
	-@echo "                        additional flags for zlc"
	-@echo "make t0001 VERBOSE=1    run test 1 and show more detail"
	-@echo "make NOCOLOR=1          run tests without ANSI color commands"

clean:
	-@rm -rf *.ml *.obc *.lci *.cmi *.cmo *.cmxi *.cmx *.o *.annot a.out
	-@rm -rf *.translation *.compilation *.ok *.test *.log *.camldebug

realclean cleanall: clean

##
FORCE:

%.debug: %.ls %.camldebug
	@cat $(<:.ls=.camldebug)
	@echo "----------------------------------------------------------------------------"
	@echo
	@FLAGS="$(ZLCFLAGS) $(ADDFLAGS) -s main					\
	    `sed -ne 's/(\*.*TEST\[\([^]]*\)\].*\*)/\1/p' $(<)`";	\
	$(ZLC) $${FLAGS} -v $< 2>&1 || true

%.camldebug: %.ls
	@echo "$$DEBUG_PRELUDE" > $@
	@echo "set arguments -I $(ZLLIB) $(ZLCFLAGS)" "../test/run/$<" >> $@

%.ml %_main.ml %.translation: %.ls FORCE
	-@FLAGS="$(ZLCFLAGS) $(ADDFLAGS) -s main			\
	    `sed -ne 's/(\*.*TEST\[\([^]]*\)\].*\*)/\1/p' $(<)`";	\
	$(ZLC) $${FLAGS} $< 2>$(<:.ls=.translation);			\
	RESULT=$$?;							\
	if [ $(VERBOSE) ]; then echo $(ZLC) $${FLAGS} $<; fi;		\
	if [ $${RESULT} -ne 0 ]; then					\
	    echo "-- run/$(<:.ls=):"					\
		 "$(S_RED)translation fail$(S_NORMAL)"			\
		 "(see $(<:.ls=.translation))";				\
	    rm -f "$(<:.ls=.ok)" "$(<:.ls=.test)";			\
	    rm -f $(<:%.ls=%)_main.ml;					\
	else								\
	    mv main.ml $(<:%.ls=%)_main.ml;				\
	fi
ifdef VERBOSE
	-@cat $(<:.ls=.translation)
endif

%.test %.compilation: %.ml %_main.ml FORCE
	-@ARGS="$(OCAMLFLAGS) -o $(<:.ml=.test) $(INCLUDES)		\
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS)			\
	    $< $(<:.ml=_main.ml)";					\
	$(OCAMLC) $${ARGS} 2>$(<:.ml=.compilation);			\
	RESULT=$$?;							\
	if [ $(VERBOSE) ]; then echo $(OCAMLC) $${ARGS}; fi;		\
	if [ -e "$(<:.ml=_main.ml)" -a $${RESULT} -ne 0 ]; then		\
	    echo "-- run/$(<:.ml=):"					\
		 "$(S_RED)compilation fail$(S_NORMAL)"			\
		 "(see $(<:.ml=.compilation))";				\
	    rm -f "$(<:.ml=.ok)" "$(<:.ml=.test)";			\
	fi
ifdef VERBOSE
	-@cat $(<:.ml=.compilation)
endif

%: %.test FORCE
	-@ARGS="-l `sed -ne 's/(\*.*ARGS\[\([^]]*\)\].*\*)/\1/p' $(<:.test=.ls)`";\
	./$(<) $${ARGS} > $(<:.test=.log) 2>&1;				\
	RESULT=$$?;							\
	if [ $(VERBOSE) ]; then echo "$(<) $${ARGS}"; fi;		\
	if [ $${RESULT} -eq 0 ]; then					\
	    echo "-- run/$(<:.test=): $(S_GREEN)ok$(S_NORMAL)";		\
	    touch $(<:.test=.ok);					\
	elif [ -e $< ]; then						\
	    echo "-- run/$(<:.test=): $(S_RED)fail$(S_NORMAL)"		\
		 "(see $(<:.test=.log))";				\
	    rm -f "$(<:.test=.ok)";					\
	fi
ifdef VERBOSE
	-@cat $(<:.test=.log)
endif

