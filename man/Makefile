# Tutorial and Manual
# Author: Marc Pouzet

include ../config
LANG=zelus
VERSION=0.1
MANUAL_HTML=zelus_html
PS2PDF=ps2pdf
PUBLIC=public
WEB_DIR=pouzet@di.ens.fr:WWW/$(LANG)
HEVEA=hevea
HACHA=hacha
PDFLATEX=pdflatex
RUNVERBATIM=./runverbatim.sh

all: zelus.pdf zelus.html 

#bibliography
zelus.bbl: zelus.aux
	$(BIBTEX) zelus

install: 
	$(INSTALL) -d $(mandir)/man1
	$(INSTALL) $(LANG).m $(mandir)/man1/$(LANG).1

clean:
	rm -f *.aux *.dvi *.log *.toc *.html *.ml *.lci *.dcc *.gz *.gif \
		*.bbl *.blg *.brf *.haux *.out ;\
	rm -r -f $(MANUAL_HTML)

realclean: clean
	rm -f zelus.pdf zelus.ps zelus.html

web: zelus.pdf zelus.html
	cp zelus.pdf $(PUBLIC)/$(LANG)-$(VERSION)_zelus.pdf
	cp zelus_html/* $(PUBLIC)/zelus-html/
	mv zelus_html/ $(LANG)-zelus
	tar -zcvf $(LANG)_zelus.tar.gz $(LANG)-$(VERSION)-zelus
	mv $(LANG)-zelus zelus_html
	mv $(LANG)_zelus.tar.gz $(PUBLIC)
	scp -r $(PUBLIC) $(WEB_DIR)

#implicit rules
.SUFFIXES: .tex .html .aux .dvi .ps .pdf

.tex.aux:
	$(PDFLATEX) $<

.tex.pdf:
	$(PDFLATEX) $<
	$(RUNVERBATIM)
	$(PDFLATEX) $<

.tex.html:
	mkdir -p $(MANUAL_HTML)
	cp zelus.css $(MANUAL_HTML)
	cp Fig/*.eps Fig/*.ps $(MANUAL_HTML)
	(cd $(MANUAL_HTML); \
	 $(HEVEA) -fix -I .. zelus.hva ../$< -o $@; \
	 $(HACHA) $@)
