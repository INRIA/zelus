include ../../config

ALL := $(shell ls t*.ls)
NTESTS := $(shell ls t*.ls | wc -l)
HALFLINE = "------------------------------"

bad: bad-quiet
	@$(MAKE) -s summary
bad-quiet: $(ALL:.ls=.log)

summary:
	@OK=`ls | grep '\.ok$$' | wc -l`;		\
	echo "$(S_BLUE)valid rejects: $$OK / $(NTESTS)"	\
	  "(`expr $$OK \\* 100 / $(NTESTS)`%)$(S_NORMAL)"

show: $(ALL:.ls=)

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
	-@echo "                        additional flags for zlc"
	-@echo "make NOCOLOR=1          run tests without ANSI color commands"
	-@echo "make showtests		show the contents of all tests"

clean:
	@-rm -f t*.lci t*.ml t*.obc t*_main.ml
	@-rm -f t*.log main.ml *.ok

realclean cleanall: clean

##

FORCE:

%: %.log ;

%.log: %.ls FORCE
	-@$(ZLC) $(ZLCFLAGS) $(ADDFLAGS) $< 2> $@;			 \
	if [ $$? -eq 0 ]; then						 \
	    echo "--bad /$(<:.ls=): $(S_RED)ERROR$(S_NORMAL)"		 \
		 "(see $(<:.ls=.log))";					 \
	    sed -ne '/(\*/d;/\*)/q;p' $<;				 \
	    rm -f "$(<:.ls=.ok)";					 \
	    echo;							 \
	elif `grep -q '^Uncaught exception:' $@`; then			 \
	    echo "--bad /$(<:.ls=): $(S_RED)ERROR$(S_NORMAL)"		 \
	    	 "(Uncaught exception, see $(<:.ls=.log))";		 \
	    rm -f "$(<:.ls=.ok)";					 \
	elif `grep -q '^Fatal error: exception Assert_failure' $@`; then \
	    echo "--bad /$(<:.ls=): $(S_RED)ERROR$(S_NORMAL)"		 \
	    	 "(Assertion failure, see $(<:.ls=.log))";		 \
	    rm -f "$(<:.ls=.ok)";					 \
	elif `grep -q '^Syntax error.' $@`; then			 \
	    echo "--bad /$(<:.ls=): $(S_RED)ERROR$(S_NORMAL)"		 \
	    	 "(Syntax error, see $(<:.ls=.log))";			 \
	    rm -f "$(<:.ls=.ok)";					 \
	else								 \
	    echo "--bad /$(<:.ls=):"					 \
		 "$(S_GREEN)correctly rejected$(S_NORMAL)";		 \
	    touch "$(<:.ls=.ok)";					 \
	fi
ifdef VERBOSE
	-@cat $(<:.ls=.log)
endif

