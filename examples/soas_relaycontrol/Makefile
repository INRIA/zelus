include ../../config

ZLEXTRALIBS = $(ZLGTKLIBS)

EXAMPLE=soas1_basic.zls \
	soas2_leadnet.zls \
	soas3_gainchanger.zls

default: $(word 1, $(targets))
all:  $(targets)
byte: $(EXAMPLE:%.zls=%.byte)
opt:  $(EXAMPLE:%.zls=%.opt)

soas.ml soas.zci: soas.zls
	$(ZELUC) $(ZELUCFLAGS) -dzero $<

soas1_basic.byte: ZLEXTRALIBS += $(ZLGTKLIBS) soas.cmo
soas1_basic.byte: soas.cmo

soas1_basic.opt: ZLEXTRALIBS += $(ZLGTKLIBS) soas.cmx
soas1_basic.opt: soas.cmx

soas1_basic.ml: soas1_basic.zls soas.zci
	$(ZELUC) $(ZELUCFLAGS) -s main -gtk2 -dzero $<
	mv main.ml $(<:.zls=)_main.ml

soas2_leadnet.byte: ZLEXTRALIBS += $(ZLGTKLIBS) soas.cmo
soas2_leadnet.byte: soas.cmo

soas2_leadnet.opt: ZLEXTRALIBS += $(ZLGTKLIBS) soas.cmx
soas2_leadnet.opt: soas.cmx

soas2_leadnet.ml: soas2_leadnet.zls soas.zci
	$(ZELUC) $(ZELUCFLAGS) -s main -sampling 0 -gtk2 -dzero $<
	mv main.ml $(<:.zls=)_main.ml

soas3_gainchanger.byte: ZLEXTRALIBS += $(ZLGTKLIBS) soas.cmo
soas3_gainchanger.byte: soas.cmo

soas3_gainchanger.opt: ZLEXTRALIBS += $(ZLGTKLIBS) soas.cmx
soas3_gainchanger.opt: soas.cmx

soas3_gainchanger.ml: soas3_gainchanger.zls soas.zci
	$(ZELUC) $(ZELUCFLAGS) -s main -sampling 0 -gtk2 -dzero $<
	mv main.ml $(<:.zls=)_main.ml

soas4_gainchanger_disc.byte: ZLEXTRALIBS += $(ZLGTKLIBS) soas.cmo
soas4_gainchanger_disc.byte: soas.cmo

soas4_gainchanger_disc.opt: ZLEXTRALIBS += $(ZLGTKLIBS) soas.cmx
soas4_gainchanger_disc.opt: soas.cmx

soas4_gainchanger_disc.ml: soas4_gainchanger_disc.zls soas.zci
	$(ZELUC) $(ZELUCFLAGS) -s main -sampling 0 -gtk2 -dzero $<
	mv main.ml $(<:.zls=)_main.ml

export:
	mkdir $(DISTDIR)/soas_relaycontrol
	cp Makefile readme.md \
	   soas1_basic.zls soas2_leadnet.zls soas3_gainchanger.zls soas.zls \
	   $(DISTDIR)/soas_relaycontrol/
	mkdir $(DISTDIR)/soas_relaycontrol/img
	cp img/*.png $(DISTDIR)/soas_relaycontrol/img/
	make -C slides
	cp slides/slides.pdf $(DISTDIR)/soas_relaycontrol/

clean:
	-@rm -f $(EXAMPLE:.zls=.ml) $(EXAMPLE:.zls=_main.ml)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci
	-@rm -f $(EXAMPLE:%.zls=%.byte) $(EXAMPLE:%.zls=%.opt)
	-@rm -f soas.ml
	-@if [ -d slides ]; then make -s -C slides clean; fi

realclean cleanall: clean

