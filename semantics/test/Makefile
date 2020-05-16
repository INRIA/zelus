ALL := $(shell ls *.zls)
NTESTS := $(shell ls *.zls | wc -l)

ZRUN=../zrun.byte
ZARGS= -s main -n 100

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

# do not remove .run files
.PRECIOUS: %.run

run: run-quiet
	@$(MAKE) -s summary

run-quiet: $(ALL:.zls=.run)

summary: 
	@RUNOK=`ls | grep '\.run.ok$$' | wc -l`; \
	printf "$(S_BLUE)run: $$RUNOK / $(NTESTS) (`expr $$RUNOK \\* 100 / $(NTESTS)`%%)$(S_NORMAL)\n"

FORCE:

check:

.SUFFIXES : .run .zls

%.run: %.zls FORCE
	@$(ZRUN) $(ZARGS) $< 1>$(<:.zls=.output) 2>$(<:.zls=.run);\
	if [ $$? -eq 0 ]; then \
	  	printf -- "$(<:.zls=): $(S_GREEN)run ok$(S_NORMAL)\n"; \
		touch "$(<:.zls=.run.ok)"; \
	else \
	 	printf -- "$(<:.zls=): $(S_RED)run fail$(S_NORMAL) (see $(<:.zls=.run))\n"; \
		rm -f "$(<:.zls.run.ok)"; \
	fi

clean:
	-@rm -r -f *.run* *.output *~
