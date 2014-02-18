#
# Makefile
#
# Do not modify. Local configuration should be done in Makefile_config
# 

TOPLEVEL =	.
include 	$(TOPLEVEL)/Makefile_ocaml
include		$(TOPLEVEL)/Makefile_config

# Default target is 'all'

all::		DEPEND DEPEND_C

all.opt::	DEPEND DEPEND_C

# cleanup includes clean'ing

cleanup::	clean

# -----------------------------------------------------------------------------
# Important Variables
# -----------------------------------------------------------------------------

# Files made in this directory from source files. They make up the
# executable.

MLL = 

MLY = 

LEXML = $(MLY:.mly=.ml) $(MLL:.mll=.ml)

LEXMLI = $(MLY:.mly=.mli)

GENERATED =  $(LEXML) $(LEXMLI)

clean::
	rm -f $(GENERATED)

LIBML = dual.ml newton.ml implicit.ml pervasives__dual.ml

LIBCMO = $(LIBML:.ml=.cmo)

AUXCMO =

LIBCMX =	$(LIBCMO:.cmo=.cmx)

ML =		$(LIBML) $(LEXML)
MLI =		$(LIBML:.ml=.mli) $(LEXMLI)

CMO =		$(ML:.ml=.cmo) $(AUXCMO)

CMX =		$(CMO:.cmo=.cmx)
OBJ =		$(CMO:.cmo=.o)
CMI =		$(CMO:.cmo=.cmi)

SOURCES =	$(ML) $(MLI)

DUALCCFILES =	dual_ml.c
DUALCHFILES =	dual_ml.h
DUALCFILES =	$(DUALCCFILES) $(DUALCHFILES)

DUALCOBJS =	$(DUALCCFILES:.c=.o)

CCFILES =	$(DUALCCFILES)
CHFILES =	$(DUALHFILES)
CFILES = 	$(CCFILES) $(CHFILES)

# Some cmo files depend on modules from mylib - make sure they are
# there.

clean::
	rm -f $(CMO) $(CMX) $(OBJ) $(CMI)

INCLUDE_DEPEND = 
INCLUDE =	
CFLAGS =		
OFLAGS =		$(CFLAGS)

#
# dependencies to libraries
#

LIBS = dual.cma

CLIBS = libdual_c.a

# -----------------------------------------------------------------------------
# Targets
# -----------------------------------------------------------------------------

#-----------------
# The library
#-----------------

dual.cma:	$(LIBCMO)
		$(CAMLC) $(CFLAGS) -a -o $@ $(LIBCMO)

dual.cmxa:	$(LIBCMX)
		$(CAMLOPT) $(OFLAGS) -a -o $@ $(LIBCMX)

all::		dual.cma

all.opt::	dual.cmxa

cleanup::
	rm -f dual.cma dual.cmxa dual.a

install::	dual.cma
	$(INSTALL) dual.cma $(LIB_DIR)

#-----------------
# The toplevel
#-----------------

all::		ocaml_dual

cleanup::
	rm -f ocaml_dual

ocaml_dual: 	$(LIBS) $(CLIBS)
	$(CAMLTOP) $(INCLUDE) -o ocaml_dual \
		-custom dual.cma unix.cma -cclib libdual_c.a

install::	ocaml_dual
	$(INSTALL) ocaml_dual $(LIB_DIR)

#-------------------------
# DUAL C low level library
#-------------------------

libdual_c.a: $(DUALCOBJS)
	ar -crs libdual_c.a $(DUALCOBJS)

cleanup::
	rm -f libdual_c.a

clean::
	rm -f $(DUALCOBJS)

install:: libdual_c.a
	$(INSTALL) libdual_c.a $(LIB_DIR)

#---------------
# Public modules
#---------------

install::	dual.cmi pervasives__dual.cmi
	$(INSTALL) dual.cmi pervasives__dual.cmi $(LIB_DIR)

#--------------
# Documentation
#--------------

doc::		dependency.svg

dependency.svg:	dependency.dot
	$(DOT) -Tsvg -odependency.svg dependency.dot

dependency.dot:	$(MLI) $(ML)
	$(CAMLDOC) -dot -dot-reduce -o dependency.dot $(MLI) $(ML)

clean::
	rm -f dependency.dot

cleanup::
	rm -f dependency.svg

# -----------------------------------------------------------------------------
# phony targets
# -----------------------------------------------------------------------------

# all code created by generators must be there before dependencies
# are calculated!

depend:		DEPEND DEPEND_C

DEPEND:		$(GENERATED) $(SOURCES)
		$(CAMLDEP) $(INCLUDE_DEPEND) $(GENERATED) $(SOURCES) > DEPEND

DEPEND_C:	$(CFILES)
		$(CC) $(CCINCLUDES) -MM $(CFILES) > DEPEND_C

tags:
		mltags *.mli $(MYLIB)/*.mli *.ml $(MYLIB)/*.ml

clean::
	rm -f tags

#
# dummy target
#

# -----------------------------------------------------------------------------
# dependencies - include manually if your make does not support include
# -----------------------------------------------------------------------------

-include DEPEND
-include DEPEND_C
