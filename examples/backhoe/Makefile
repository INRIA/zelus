include ../../config

ZLEXTRALIBS = $(ZLGTKLIBS)

backhoe.byte: INCLUDES += $(LABLGTK2) $(SUNDIALS)
backhoe.byte: backhoegui.cmo backhoedyn.cmo backhoecontrol.cmo backhoe_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) $^ 

backhoedyn.zls: backhoegui.zci

backhoegui.cmi backhoegui.cmo: INCLUDES += $(LABLGTK2)
backhoegui.cmi: backhoegui.mli
backhoegui.cmo: backhoegui.ml backhoegui.cmi

backhoegui.zci: backhoegui.zli

backhoedyn.cmi backhoedyn.cmo: backhoedyn.ml
backhoedyn.ml backhoedyn.zci: backhoedyn.zls backhoegui.zci
	$(ZELUC) -i $(ZELUCFLAGS) $<

backhoecontrol.ml backhoe_main.ml: backhoecontrol.zls backhoedyn.zci
	$(ZELUC) -i $(ZELUCFLAGS) -gtk2 -s main $<
	mv main.ml backhoe_main.ml

test: backhoegui.cmi backhoegui.ml
	@cp backhoegui.ml backhoegui_test.ml
	@printf "let _ = runtest () ;;\n" >> backhoegui_test.ml
	$(OCAMLC) -o test $(LABLGTK2) lablgtk.cma gtkInit.cmo \
	    backhoegui_test.ml

export:
	mkdir $(DISTDIR)/backhoe
	cp backhoecontrol.zls backhoedyn.zls backhoegui.zli backhoegui.ml \
	   backhoegui.mli Makefile readme.md \
	   $(DISTDIR)/backhoe/
	mkdir $(DISTDIR)/backhoe/img
	cp img/*.png $(DISTDIR)/backhoe/img/
	make -C slides
	cp slides/slides.pdf $(DISTDIR)/backhoe/

clean realclean cleanall:
	-@rm -f backhoe_main.ml backhoedyn.ml backhoecontrol.ml
	-@rm -f backhoegui_test.ml
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci
	-@rm -f backhoe backhoe.byte backhoe.opt
	-@if [ -d slides ]; then make -s -C slides clean; fi

