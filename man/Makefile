# Tutorial and Manual
# Author: Marc Pouzet

include ../config
LANG=zelus
VERSION=1.2
MANUAL_HTML=zelus_html
PS2PDF=ps2pdf
PUBLIC=public
WEB_DIR=pouzet@di.ens.fr:WWW/$(LANG)
HEVEA=hevea
HACHA=hacha
PDFLATEX=pdflatex
LATEXMK=latexmk -pdf

RUNVERBATIM=runverbatim/runverbatim.sh

all:
	pdflatex manual.tex

re: manual.pdf 
	$(LATEXMK) manual.tex

#runverbatim
runverbatim: manual.aux
	$(RUNVERBATIM)

#bibliography
manual.bbl: manual.aux
	$(BIBTEX) manual

install: 

clean:
	rm -f *.aux *.log *.toc *.html *.ml *.zci *.gz *.gif \
		*.bbl *.blg *.brf *.haux *.out ;\
	rm -r -f $(MANUAL_HTML)

realclean: clean
	rm -f zelus.pdf zelus.ps zelus.html

web: manual.pdf manual.html
	cp manual.pdf $(PUBLIC)/$(LANG)-$(VERSION)_zelus.pdf
	cp manual_html/* $(PUBLIC)/zelus-html/
	mv manual_html/ $(LANG)-zelus
	tar -zcvf $(LANG)_zelus.tar.gz $(LANG)-$(VERSION)-zelus
	mv $(LANG)-zelus zelus_html
	mv $(LANG)_zelus.tar.gz $(PUBLIC)
	scp -r $(PUBLIC) $(WEB_DIR)

#implicit rules
.SUFFIXES: .tex .html .aux .ps .pdf

.tex.aux:
	$(PDFLATEX) $<

.tex.pdf:
	$(PDFLATEX) $<
	$(PDFLATEX) $<

.tex.html:
	mkdir -p $(MANUAL_HTML)
	cp zelus.css $(MANUAL_HTML)
	cp Fig/*.eps Fig/*.ps $(MANUAL_HTML)
	(cd $(MANUAL_HTML); \
	 $(HEVEA) -fix -I .. zelus.hva ../$< -o $@; \
	 $(HACHA) $@)
