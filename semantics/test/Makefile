ALL := $(shell ls *.zls)
NTESTS := $(shell ls *.zls | wc -l)

ZRUN=../zrun.byte
ZRUNOPT= -s main -n 10

ifdef NOCOLOR
    S_BLUE   = ""
    S_GREEN  = ""
    S_RED    = ""
    S_NORMAL = ""
else
    S_BLUE   = "\\033[34m"
    S_GREEN  = "\\033[32m"
    S_RED    = "\\033[31m"
    S_NORMAL = "\\033[0m"
endif

run: $(ALL:.zls=.run)
	@RUNOK=`ls | grep '\.run.ok$$' | wc -l`; \
	printf "run: $$RUNOK / $(NTESTS) (`expr $$RUNOK \\* 100 / $(NTESTS)`%%)$(S_NORMAL)\n"

check:

.SUFFIXES : .run .zls

%.run: %.zls
	$(ZRUN) $(ZRUNOPT) $< 2>$(<:.zls=.run);
	if [ $$? -eq 0 ]; then
	   printf -- "$(<:.zls=): run ok\n";\
	   touch "$(<:.zls=.run.ok)";
	else
	   printf -- "$(<:.zls=): run fail (see $(<:.zls=.run))\n"; \
	   rm -f "$(<:.zls.run.ok)";

clean:
	rm -r -f *.run*
