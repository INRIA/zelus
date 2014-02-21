include ../../config

ALL := $(shell ls t*.zls)
NTESTS := $(shell ls t*.zls | wc -l)
HALFLINE = "------------------------------"

bad: bad-quiet
	@$(MAKE) -s summary
bad-quiet: $(ALL:.zls=.log)

summary:
	@OK=`ls | grep '\.ok$$' | wc -l`;		\
	echo "$(S_BLUE)valid rejects: $$OK / $(NTESTS)"	\
	  "(`expr $$OK \\* 100 / $(NTESTS)`%)$(S_NORMAL)"

show: $(ALL:.zls=)

showtests:
	@for f in $(ALL); do				\
	    echo "-----$(HALFLINE)$(HALFLINE)-bad/$$f";	\
	    cat $$f;					\
	    echo;					\
	done

help:
	-@echo "make                    run all tests"
	-@echo "make t0001 t0004        run tests 1 and 4"
	-@echo "make t0001 VERBOSE=1    run test 1 and show more detail"
	-@echo "make ADDFLAGS=-noinit t0004.debug"
	-@echo "                        additional flags for zeluc"
	-@echo "make NOCOLOR=1          run tests without ANSI color commands"
	-@echo "make showtests		show the contents of all tests"

clean:
	@-rm -f t*.lci t*.ml t*.obc t*_main.ml
	@-rm -f t*.log main.ml *.ok

realclean cleanall: clean

##

FORCE:

%: %.log ;

%.log: %.zls FORCE
	-@$(ZELUC) $(ZELUCFLAGS) $(ADDFLAGS) $< 2> $@;			 \
	if [ $$? -eq 0 ]; then						 \
	    echo "--bad /$(<:.zls=): $(S_RED)ERROR$(S_NORMAL)"		 \
		 "(see $(<:.zls=.log))";					 \
	    sed -ne '/(\*/d;/\*)/q;p' $<;				 \
	    rm -f "$(<:.zls=.ok)";					 \
	    echo;							 \
	elif `grep -q '^Uncaught exception:' $@`; then			 \
	    echo "--bad /$(<:.zls=): $(S_RED)ERROR$(S_NORMAL)"		 \
	    	 "(Uncaught exception, see $(<:.zls=.log))";		 \
	    rm -f "$(<:.zls=.ok)";					 \
	elif `grep -q '^Fatal error: exception Assert_failure' $@`; then \
	    echo "--bad /$(<:.zls=): $(S_RED)ERROR$(S_NORMAL)"		 \
	    	 "(Assertion failure, see $(<:.zls=.log))";		 \
	    rm -f "$(<:.zls=.ok)";					 \
	elif `grep -q '^Syntax error.' $@`; then			 \
	    echo "--bad /$(<:.zls=): $(S_RED)ERROR$(S_NORMAL)"		 \
	    	 "(Syntax error, see $(<:.zls=.log))";			 \
	    rm -f "$(<:.zls=.ok)";					 \
	else								 \
	    echo "--bad /$(<:.zls=):"					 \
		 "$(S_GREEN)correctly rejected$(S_NORMAL)";		 \
	    touch "$(<:.zls=.ok)";					 \
	fi
ifdef VERBOSE
	-@cat $(<:.zls=.log)
endif

