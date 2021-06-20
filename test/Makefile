
.PHONY: good bad run

all: bad-quiet good-quiet run-quiet
	@(cd bad;  $(MAKE) -s summary)
	@(cd good; $(MAKE) -s summary)
	@(cd run;  $(MAKE) -s summary)

good:
	@(cd good; $(MAKE) -s compilation)

good-quiet:
	@(cd good; $(MAKE) -s compilation-quiet)

bad:
	@(cd bad; $(MAKE) -s bad)

bad-quiet:
	@(cd bad; $(MAKE) -s bad-quiet)

run:
	@(cd run; $(MAKE) -s run)

run-quiet:
	@(cd run; $(MAKE) -s run-quiet)

showtests:
	@(cd bad;  $(MAKE) -s showtests)
	@(cd good; $(MAKE) -s showtests)
	@(cd run;  $(MAKE) -s showtests)

clean:
	$(MAKE) -s -C good clean
	$(MAKE) -s -C bad clean
	$(MAKE) -s -C run clean

realclean cleanall:
	$(MAKE) -s -C good cleanall
	$(MAKE) -s -C bad cleanall
	$(MAKE) -s -C run cleanall

