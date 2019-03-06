DIRS = $(shell ls -d */)

all:
	@for dir in $(DIRS); do $(MAKE) -C $$dir all; done
opt:
	@for dir in $(DIRS); do $(MAKE) -C $$dir opt; done
byte:
	@for dir in $(DIRS); do $(MAKE) -C $$dir byte; done
spec:
	@for dir in $(DIRS); do $(MAKE) -C $$dir spec; done
check:
	@for dir in $(DIRS); do $(MAKE) -C $$dir check; done
clean:
	@for dir in $(DIRS); do $(MAKE) -C $$dir clean; done
cleanall:
	@for dir in $(DIRS); do $(MAKE) -C $$dir cleanall; done
realclean:
	@for dir in $(DIRS); do $(MAKE) -C $$dir cleanall; done
