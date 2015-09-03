# Tutorial and Manual
# Author: Marc Pouzet
# 	  Timothy Bourke

include ../config
LANG=zelus
VERSION=1.2
WWWMAN=wwwman
PS2PDF=ps2pdf
HEVEA=hevea
HACHA=hacha
IMAGEN=imagen
PDFLATEX=pdflatex
XSLTPROC=xsltproc
BIBTEX=bibtex
LATEXMK=latexmk -pdf

CHECKLISTINGS=./checklistings.sh

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
	$(PDFLATEX) manual

### Generating the web pages

# 1. Generate a basic page with HeVeA.
$(WWWMAN)/manual.html: manual.tex manual.bbl manual.pdf samples/tutorial0001.html
	mkdir -p $(WWWMAN)
	cp manual.bbl $(WWWMAN)/
	$(HEVEA) -fix zelus.hva $< -o $@
	for f in $(WWWMAN)/*.png; do		\
		mv $$f $$f.lowres;		\
	done
	$(IMAGEN) -res 200 $(@:.html=)
	for f in $(WWWMAN)/*.png; do		\
		mv $$f $${f%.png}@2x.png;	\
		mv $$f.lowres $${f};		\
	done
	rm $(WWWMAN)/manual.bbl

# 2. Cut it up into pieces with HaChA.
$(WWWMAN)/index.html: $(WWWMAN)/manual.html
	cd $(WWWMAN) && $(HACHA) $(notdir $<)

# 3. Integrate into the main website (using xlst).
wwwman: $(WWWMAN)/index.html css js \
    inc-header.html inc-javascript.html inc-titlebar.html
	@if [ ! -f "$@/manual.haux" ]; then			   	   \
	    printf >&2 'wwwman: %s\n'					   \
	    	"cannot transform twice! (re-make $(WWWMAN)/manual.html)"; \
	    exit 1;							   \
	fi
	mkdir -p $@
	for f in $$(ls $@/*.html); do			       	   	   \
	    $(XSLTPROC) --output $@/$${f#*/}.2 --html			   \
	    	--param isindex `if [ "$$f" = "$(WWWMAN)/index.html" ];    \
	    	     		 then echo 1; else echo 0; fi`		   \
	    	--param issingle `if [ "$$f" = "$(WWWMAN)/manual.html" ];  \
	    	      		  then echo 1; else echo 0; fi`		   \
	    	mantosite.xsl $$f					   \
		  && mv $@/$${f#*/}.2 $@/$${f#*/};			   \
	done
	cp Fig/bouncingball.png $@/
	convert $@/bouncingball.png -scale '200%' $@/bouncingball@2x.png
	cp manual.pdf $@/
	rm -f $@/contents_motif.gif $@/next_motif.gif $@/previous_motif.gif
	rm -f $@/manual.haux $@/manual.htoc $@/manual.image.tex
	chmod o+r $@/*

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

###

clean:
	rm -f *.aux *.log *.toc *.html *.ml *.zci *.gz *.gif \
		*.bbl *.blg *.brf *.haux *.out ;\
	rm -rf inc-header.html inc-javascript.html

realclean: clean
	rm -f zelus.pdf zelus.ps zelus.html
	rm -rf $(WWWMAN) css js

#implicit rules
.SUFFIXES: .tex .html .aux .ps .pdf

.tex.aux:
	$(PDFLATEX) $<

.tex.pdf:
	$(PDFLATEX) $<
	$(PDFLATEX) $<

