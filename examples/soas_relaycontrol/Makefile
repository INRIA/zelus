include ../../config

ZLEXTRALIBS = $(ZLGTKLIBS)

EXAMPLE=soas1_basic.ls \
	soas2_leadnet.ls \
	soas3_gainchanger.ls

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.ls=%.byte)
opt:  $(EXAMPLE:%.ls=%.opt)

soas.ml soas.lci: soas.ls
	$(ZLC) $(ZLCFLAGS) -dzero -period $<

soas1_basic.byte: ZLEXTRALIBS += $(ZLGTKLIBS) soas.cmo
soas1_basic.byte: soas.cmo

soas1_basic.opt: ZLEXTRALIBS += $(ZLGTKLIBS) soas.cmx
soas1_basic.opt: soas.cmx

soas1_basic.ml: soas1_basic.ls soas.lci
	$(ZLC) $(ZLCFLAGS) -s main -sampling 0 -gtk2 -dzero -period $<
	mv main.ml $(<:.ls=)_main.ml

soas2_leadnet.byte: ZLEXTRALIBS += $(ZLGTKLIBS) soas.cmo
soas2_leadnet.byte: soas.cmo

soas2_leadnet.opt: ZLEXTRALIBS += $(ZLGTKLIBS) soas.cmx
soas2_leadnet.opt: soas.cmx

soas2_leadnet.ml: soas2_leadnet.ls soas.lci
	$(ZLC) $(ZLCFLAGS) -s main -sampling 0 -gtk2 -dzero -period $<
	mv main.ml $(<:.ls=)_main.ml

soas3_gainchanger.byte: ZLEXTRALIBS += $(ZLGTKLIBS) soas.cmo
soas3_gainchanger.byte: soas.cmo

soas3_gainchanger.opt: ZLEXTRALIBS += $(ZLGTKLIBS) soas.cmx
soas3_gainchanger.opt: soas.cmx

soas3_gainchanger.ml: soas3_gainchanger.ls soas.lci
	$(ZLC) $(ZLCFLAGS) -s main -sampling 0 -gtk2 -dzero -period $<
	mv main.ml $(<:.ls=)_main.ml

export:
	mkdir $(DISTDIR)/soas_relaycontrol
	cp Makefile readme.md \
	   soas1_basic.ls soas2_leadnet.ls soas3_gainchanger.ls soas.ls \
	   $(DISTDIR)/soas_relaycontrol/
	mkdir $(DISTDIR)/soas_relaycontrol/img
	cp img/*.png $(DISTDIR)/soas_relaycontrol/img/
	make -C slides
	cp slides/slides.pdf $(DISTDIR)/soas_relaycontrol/

clean:
	-@rm -f $(EXAMPLE:.ls=.ml) $(EXAMPLE:.ls=_main.ml)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.lci
	-@rm -f $(EXAMPLE:%.ls=%.byte) $(EXAMPLE:%.ls=%.opt)
	-@rm -f soas.ml
	-@if [ -d slides ]; then make -s -C slides clean; fi

realclean cleanall: clean

