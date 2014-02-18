
DIRS=`find . -mindepth 1 -maxdepth 1 -type d \! -name .svn`

.PHONY: all clean realclean

all:
	@for i in ${DIRS}; do ${MAKE} -C $$i all; done;
byte:
	@for i in ${DIRS}; do ${MAKE} -C $$i byte; done;
opt:
	@for i in ${DIRS}; do ${MAKE} -C $$i opt; done;
export:
	@for i in ${DIRS}; do ${MAKE} -C $$i export; done;
clean:
	@for i in ${DIRS}; do ${MAKE} -C $$i clean; done;
realclean cleanall: clean
	@for i in ${DIRS}; do ${MAKE} -C $$i realclean; done;

