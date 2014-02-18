include config

MLOBJ=  sundials.cmo 		\
	nvector.cmo 		\
	nvector_array.cmo 	\
	cvode.cmo 		\
	cvode_nvector.cmo	\
	cvode_serial.cmo

COBJ=	cvode_ml$(XO) 		\
	cvode_ml_ba$(XO) 	\
	cvode_ml_nvec$(XO) 	\
	nvector_ml$(XO)

INSTALL_FILES= 			\
    META			\
    $(MLOBJ:.cmo=.cmi)		\
    libmlsundials_cvode$(XA)	\
    sundials_cvode$(XA)		\
    sundials_cvode.cma		\
    sundials_cvode.cmxa

STUBLIBS=dllmlsundials_cvode$(XS)

CFLAGS+=-fPIC

# ##

.PHONY: all sundials_cvode install doc

all: sundials_cvode.cma sundials_cvode.cmxa

sundials_cvode.cma sundials_cvode.cmxa: $(MLOBJ) $(MLOBJ:.cmo=.cmx) $(COBJ)
	$(OCAMLMKLIB) $(OCAMLMKLIBFLAGS) \
	    -o sundials_cvode -oc mlsundials_cvode $^ \
	    -lsundials_cvode $(LAPACK_LIB) -lsundials_nvecserial

cvode_nvector.mli: cvode_serial.mli cvode_nvector.doc
	$(SED) \
	-e "/^type \(val_array\|der_array\) =/d"			\
	-e "s/ session\( \|\$\)/ 'a session\1/g"			\
	-e "s/\([ (]\)\([^ ]*\) jacobian_arg\([ )]\|\$\)/\1(\2, 'a) jacobian_arg\3/g" \
	-e "s/\([ (]\)val_array\([ )]\|\$\)/\1'a\2/g"			\
	-e "s/\([ (]\)der_array\([ )]\|\$\)/\1'a\2/g"			\
	-e "s/\([ (]\)nvec\([ )]\|\$\)/\1'a nvector\2/g"		\
	-e "s/\([ (]\)solve_arg\([ )]\|\$\)/\1'a solve_arg\2/g"		\
	-e "s/\([ (]\)single_tmp\([ )]\|\$\)/\1'a single_tmp\2/g"	\
	-e "s/\([ (]\)triple_tmp\([ )]\|\$\)/\1'a triple_tmp\2/g"	\
	-e "s/^\(type 'a nvector = \).*/\1'a Nvector.nvector/"		\
	-e "/(\*ENDINTRO\*)/r cvode_nvector.doc"			\
	-e "/^(\*STARTINTRO\*)/,/(\*ENDINTRO\*)/d"				\
	$< > $@

cvode.o: cvode_ml.c
cvode_ml_ba.o: cvode_ml_nvec.c
	$(CC) -I $(OCAML_INCLUDE) $(CFLAGS) -DCVODE_ML_BIGARRAYS -o $@ -c $<
cvode_ml_nvec.o: cvode_ml_nvec.c
nvector_ml.o: nvector_ml.c

dochtml.cmo: INCLUDES += -I +ocamldoc

META: META.in
	@$(ECHO) "version = \"$(VERSION)\"" > $@
	@$(CAT) $< >> $@

doc: doc/html/index.html

doc/html/index.html: dochtml.cmo \
    		     $(MLOBJ:.cmo=.mli) $(MLOBJ:.cmo=.cmi) \
		     intro.doc cvode_nvector.doc
	$(OCAMLDOC) -g dochtml.cmo \
	    -cvode-doc-root "$(CVODE_DOC_ROOT)" \
	    -pp "$(DOCPP)"		\
	    -d ./doc/html/		\
	    -t "Sundials (-CVODE)"	\
	    -intro intro.doc		\
	    $(MLOBJ:.cmo=.mli)

# ##

install: sundials_cvode.cma sundials_cvode.cmxa META
	$(MKDIR) $(PKGDIR)
	$(CP) $(INSTALL_FILES) $(PKGDIR)
	$(CP) $(STUBLIBS) $(STUBDIR)
ifeq ($(INSTALL_DOCS), 1)
	$(MKDIR) $(DOCDIR)/html
	$(CP) doc/html/style.css doc/html/*.html $(DOCDIR)/html/
endif

uninstall:
	for f in $(STUBLIBS); do	 \
	    $(RM) $(STUBDIR)$$f || true; \
	done
	for f in $(INSTALL_FILES); do	 \
	    $(RM) $(PKGDIR)$$f || true;  \
	done
	-$(RMDIR) $(PKGDIR)
ifeq ($(INSTALL_DOCS), 1)
	-$(RM) $(DOCDIR)/html/style.css $(DOCDIR)/html/*.html
	-$(RMDIR) $(DOCDIR)/html
	-$(RMDIR) $(DOCDIR)
endif

ocamlfind: sundials_cvode.cma sundials_cvode.cmxa META
	ocamlfind install sundials $(INSTALL_FILES) $(STUBLIBS)

# ##

depend: .depend
.depend: cvode_nvector.mli
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

clean:
#	-@$(MAKE) -C examples clean
	-@$(RM) -f $(MLOBJ) $(MLOBJ:.cmo=.cmx) $(MLOBJ:.cmo=.o)
	-@$(RM) -f $(COBJ) cvode.annot
	-@$(RM) -f $(MLOBJ:.cmo=.cma) $(MLOBJ:.cmo=.cmxa)
	-@$(RM) -f sundials_cvode$(XA)
	-@$(RM) -f dochtml.cmi dochtml.cmo

cleandoc:
	-@$(RM) -f doc/html/*.html doc/html/style.css

realclean: cleanall
cleanall: clean
#	-@$(MAKE) -C examples cleanall
	-@$(RM) -f $(MLOBJ:.cmo=.cmi)
	-@$(RM) -f sundials_cvode.cma sundials_cvode.cmxa
	-@$(RM) -f libmlsundials_cvode$(XA) dllmlsundials_cvode$(XS)
	-@$(RM) -f META

-include .depend
