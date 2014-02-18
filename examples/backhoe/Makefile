include ../../config

ZLEXTRALIBS = $(ZLGTKLIBS)

backhoe.byte: INCLUDES += $(LABLGTK2) $(SUNDIALS)
backhoe.byte: backhoegui.cmo backhoedyn.cmo backhoecontrol.cmo backhoe_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(INCLUDES) \
	    -I $(ZLLIB) $(ZLSTDLIBS) $(ZLEXTRALIBS) $^ 

backhoedyn.ls: backhoegui.lci

backhoegui.cmi backhoegui.cmo: INCLUDES += $(LABLGTK2)
backhoegui.cmi: backhoegui.mli
backhoegui.cmo: backhoegui.ml backhoegui.cmi

backhoegui.lci: backhoegui.lsi

backhoedyn.cmi backhoedyn.cmo: backhoedyn.ml
backhoedyn.ml backhoedyn.lci: backhoedyn.ls backhoegui.lci
	$(ZLC) -i $(ZLCFLAGS) -period $<

backhoecontrol.ml backhoe_main.ml: backhoecontrol.ls backhoedyn.lci
	$(ZLC) -i $(ZLCFLAGS) -period -gtk2 -sampling 5 -s main $<
	mv main.ml backhoe_main.ml

test: backhoegui.cmi backhoegui.ml
	@cp backhoegui.ml backhoegui_test.ml
	@echo "let _ = runtest () ;;" >> backhoegui_test.ml
	$(OCAMLC) -o test $(LABLGTK2) lablgtk.cma gtkInit.cmo \
	    backhoegui_test.ml

export:
	mkdir $(DISTDIR)/backhoe
	cp backhoecontrol.ls backhoedyn.ls backhoegui.lsi backhoegui.ml \
	   backhoegui.mli Makefile readme.md \
	   $(DISTDIR)/backhoe/
	mkdir $(DISTDIR)/backhoe/img
	cp img/*.png $(DISTDIR)/backhoe/img/
	make -C slides
	cp slides/slides.pdf $(DISTDIR)/backhoe/

clean realclean cleanall:
	-@rm -f backhoe_main.ml backhoedyn.ml backhoecontrol.ml
	-@rm -f backhoegui_test.ml
	-@rm -f *.o *.cm[oix] *.annot *.obc *.lci
	-@rm -f backhoe backhoe.byte backhoe.opt
	-@if [ -d slides ]; then make -s -C slides clean; fi

