ALL := $(shell ls *.zlus)
NTESTS := $(shell ls *.zlus | wc -l)

MAIN=../zeluc.exe
ZARGS= -I ../lib/std

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

run-quiet: $(ALL:.zlus=.run)

summary: 
	@RUNOK=`ls | grep '\.run.ok$$' | wc -l`; \
	printf "$(S_BLUE)run: $$RUNOK / $(NTESTS) (`expr $$RUNOK \\* 100 / $(NTESTS)`%%)$(S_NORMAL)\n"

FORCE:

check:

.SUFFIXES : .run .zlus

%.run: %.zlus FORCE
	@$(MAIN) $(ZARGS) $< 1>$(<:.zlus=.output) 2>$(<:.zlus=.run);\
	if [ $$? -eq 0 ]; then \
	  	printf -- "$(<:.zlus=): $(S_GREEN)run ok$(S_NORMAL)\n"; \
		touch "$(<:.zlus=.run.ok)"; \
	else \
	 	printf -- "$(<:.zlus=): $(S_RED)run fail$(S_NORMAL) (see $(<:.zlus=.run))\n"; \
		rm -f "$(<:.zlus.run.ok)"; \
	fi

clean:
	-@rm -r -f *.run* *.output *~
