
all: checklistings.sty checklistings.pdf

checklistings.pdf: checklistings.dtx checklistings.ind checklistings.sty \
    		   checklistings.chkl
	./checklistings.sh checklistings.chkl
	pdflatex $<
	pdflatex $<

checklistings.ind: checklistings.idx
	makeindex -s gind.ist -o $@ $<

checklistings.idx checklistings.chkl: checklistings.dtx
	pdflatex $<

checklistings.sty: checklistings.dtx
	latex checklistings.ins

example.pdf: example.tex example.chkl checklistings.sty
	./checklistings.sh example.chkl
	pdflatex $<
	pdflatex $<

example.html: example.tex example.chkl checklistings.hva
	./checklistings.sh example.chkl
	hevea -fix example

example.chkl: example.tex
	pdflatex $<

clean:
	-@rm -rf chklisting0*.tex chklisting0*.ml Withopen*
	-@rm -rf chklisting0*.msg chklisting0*.err
	-@rm -rf checklistings.aux checklistings.glo checklistings.idx
	-@rm -rf checklistings.ilg checklistings.ind checklistings.log
	-@rm -rf checklistings.chkl checklistings.tmp
	-@rm -rf checklistings.hd checklistings.out
	-@rm -rf example0*.tex example0*.ml
	-@rm -rf example0*.msg example0*.err example0*.html
	-@rm -rf example.aux example.log
	-@rm -rf example.chkl example.tmp

