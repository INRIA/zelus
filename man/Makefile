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
XSLTPROC=xsltproc
BIBTEX=bibtex
LATEXMK=latexmk -pdf

CHECKLISTINGS=checklistings/checklistings.sh

.PHONY: wwwman

all:
	pdflatex manual.tex

re: manual.pdf
	$(LATEXMK) manual.tex

manual.pdf: manual.tex manual.bbl samples/tutorial0001.tex
	$(PDFLATEX) manual

#checklistings
checklistings: manual.chkl
	$(CHECKLISTINGS) $<

samples/tutorial0001.html: manual.chkl
	$(CHECKLISTINGS) $<

#bibliography
manual.bbl:
	$(PDFLATEX) manual
	$(BIBTEX) manual

install: 

$(MANUAL_HTML)/manual.html: manual.tex manual.pdf samples/tutorial0001.html
	mkdir -p $(MANUAL_HTML)/Fig
	cp zelus.css $(MANUAL_HTML)
	cp hevea.sty $(MANUAL_HTML)
	cp checklistings.sty $(MANUAL_HTML)
	cp Fig/*.eps Fig/*.ps $(MANUAL_HTML)/Fig/
	(cd $(MANUAL_HTML); \
	 $(HEVEA) -fix -I .. zelus.hva ../$< -o $(notdir $@); \
	 $(HACHA) $(notdir $@))

wwwman: $(MANUAL_HTML)/manual.html css js \
    inc-header.html inc-javascript.html inc-titlebar.html
	mkdir -p $@
	$(XSLTPROC) --output $@/index.html --html --param isindex 1 \
		mantosite.xsl $(MANUAL_HTML)/index.html
	$(XSLTPROC) --output $@/manual.html --html --param issingle 1 \
		mantosite.xsl $(MANUAL_HTML)/manual.html
	for f in $$(ls $(MANUAL_HTML)/manual0*.html);\
	do $(XSLTPROC) --output $@/$${f#*/} --html mantosite.xsl $$f; done
	cp $(MANUAL_HTML)/*.png $@/
	cp manual.pdf $@/

css:
	ln -s ../www/www/$@

js:
	ln -s ../www/www/$@

inc-header.html: ../www/src/inc-header.html
	@printf '<head>' > $@
	@sed -e 's#<meta\(.*\)>#<meta\1 />#'	\
	     -e 's#<link\(.*\)>#<link\1 />#'	\
	     -e 's#./css/#../css/#'		\
	     -e 's#./js/#../js/#'		\
	    $< >> $@
	@printf '</head>' >> $@

inc-javascript.html: ../www/src/inc-javascript.html
	@printf '<contents>' > $@
	@sed -e 's#<meta\(.*\)>#<meta\1 />#'	\
	     -e 's#./js/#../js/#'		\
	    $< >> $@
	@printf '</contents>' >> $@

inc-titlebar.html: ../www/src/inc-titlebar.html
	cp $< $@

web: manual.pdf $(MANUAL_HTML)/manual.html
	mkdir -p $(PUBLIC)
	cp manual.pdf $(PUBLIC)/$(LANG)-$(VERSION)_zelus.pdf
	cp -r $(MANUAL_HTML) $(PUBLIC)/zelus-html
	mv $(MANUAL_HTML)/ $(LANG)-zelus
	tar -zcvf $(LANG)_zelus.tar.gz $(LANG)-$(VERSION)-zelus
	mv $(LANG)-zelus zelus_html
	mv $(LANG)_zelus.tar.gz $(PUBLIC)
	scp -r $(PUBLIC) $(WEB_DIR)

clean:
	rm -f *.aux *.log *.toc *.html *.ml *.zci *.gz *.gif \
		*.bbl *.blg *.brf *.haux *.out ;\
	rm -rf inc-header.html inc-javascript.html
	rm -r -f $(MANUAL_HTML)

realclean: clean
	rm -f zelus.pdf zelus.ps zelus.html
	rm -rf wwwman css js

#implicit rules
.SUFFIXES: .tex .html .aux .ps .pdf

.tex.aux:
	$(PDFLATEX) $<

.tex.pdf:
	$(PDFLATEX) $<
	$(PDFLATEX) $<

