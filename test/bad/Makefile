include ../color

ALL := $(shell ls *.zlus)
NTESTS := $(shell ls *.zlus | wc -l)
HALFLINE = "------------------------------"

bad: bad-quiet
	@$(MAKE) -s summary
bad-quiet: $(ALL:.zlus=.log)

summary:
	@OK=`ls | grep '\.ok$$' | wc -l`;		\
	printf "$(S_BLUE)valid rejects: $$OK / $(NTESTS) (`expr $$OK \\* 100 / $(NTESTS)`%%)$(S_NORMAL)\n"

show: $(ALL:.zlus=)

showtests:
	@for f in $(ALL); do					\
	    printf -- "-----$(HALFLINE)$(HALFLINE)-bad/$$f\n";	\
	    cat $$f;						\
	    printf "\n";					\
	done

help:
	-@printf "make                    run all tests\n"
	-@printf "make t0001 t0004        run tests 1 and 4\n"
	-@printf "make t0001 VERBOSE=1    run test 1 and show more detail\n"
	-@printf "make ADDFLAGS=-noinit t0004.debug\n"
	-@printf "                        additional flags for zeluc\n"
	-@printf "make NOCOLOR=1          run tests without ANSI color commands\n"
	-@printf "make showtests		show the contents of all tests\n"

clean:
	@-rm -f t*.zci t*.ml t*.obc t*_main.ml
	@-rm -f t*.log main.ml *.ok

realclean cleanall: clean

##

FORCE:

%: %.log ;

%.log: %.zlus FORCE
	-@$(ZELUC) $(ZELUCFLAGS) $(ADDFLAGS) $< 2> $@;			 \
	if [ $$? -eq 0 ]; then						 \
	    printf -- "--bad /$(<:.zlus=): $(S_RED)ERROR$(S_NORMAL) (see $(<:.zlus=.log))\n";				 \
	    sed -ne '/(\*/d;/\*)/q;p' $<;				 \
	    rm -f "$(<:.zlus=.ok)";					 \
	    printf "\n";						 \
	elif `grep -q '^Uncaught exception:' $@`; then			 \
	    printf -- "--bad /$(<:.zlus=): $(S_RED)ERROR$(S_NORMAL) (Uncaught exception, see $(<:.zlus=.log))\n";	 \
	    rm -f "$(<:.zlus=.ok)";					 \
	elif `grep -q '^Fatal error: exception Assert_failure' $@`; then \
	    printf -- "--bad /$(<:.zlus=): $(S_RED)ERROR$(S_NORMAL) (Assertion failure, see $(<:.zlus=.log))\n"; \
	    rm -f "$(<:.zlus=.ok)";					 \
	elif `grep -q '^Syntax error.' $@`; then			 \
	    printf -- "--bad /$(<:.zlus=): $(S_RED)ERROR$(S_NORMAL) (Syntax error, see $(<:.zlus=.log))\n"; \
	    rm -f "$(<:.zlus=.ok)";					 \
	elif `grep -q '^Fatal error: cannot find file.*zeluc.byte' $@`; then			 \
	    printf -- "--bad /$(<:.zlus=): $(S_RED)SYSTEM ERROR$(S_NORMAL) (zeluc.byte not found)\n"; \
	    rm -f "$(<:.zlus=.ok)";					 \
	else								 \
	    printf -- "--bad /$(<:.zlus=): $(S_GREEN)correctly rejected$(S_NORMAL)\n"; \
	    touch "$(<:.zlus=.ok)";					 \
	fi
ifdef VERBOSE
	-@cat $(<:.zlus=.log)
endif

