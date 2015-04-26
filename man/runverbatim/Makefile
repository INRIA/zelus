
all: runverbatim.sty runverbatim.pdf

runverbatim.pdf: runverbatim.dtx runverbatim.ind runverbatim.sty runverbatim.rvrb
	./runverbatim.sh runverbatim.rvrb
	pdflatex $<
	pdflatex $<

runverbatim.ind: runverbatim.idx
	makeindex -s gind.ist -o $@ $<

runverbatim.idx runverbatim.rvrb: runverbatim.dtx
	pdflatex $<

runverbatim.sty:
	latex runverbatim.ins

example.pdf: example.tex example.rvrb runverbatim.sty
	./runverbatim.sh example.rvrb
	pdflatex $<
	pdflatex $<

example.html: example.tex example.rvrb runverbatim.hva
	./runverbatim.sh example.rvrb
	hevea -fix example

example.rvrb: example.tex
	pdflatex $<

clean:
	-@rm -rf runverbatim0*.tex runverbatim0*.ml Withopen*
	-@rm -rf runverbatim0*.msg runverbatim0*.err
	-@rm -rf runverbatim.aux runverbatim.glo runverbatim.idx
	-@rm -rf runverbatim.ilg runverbatim.ind runverbatim.log
	-@rm -rf runverbatim.rvrb runverbatim.tmp
	-@rm -rf runverbatim.hd runverbatim.out
	-@rm -rf example0*.tex example0*.ml
	-@rm -rf example0*.msg example0*.err
	-@rm -rf example.aux example.log
	-@rm -rf example.rvrb example.tmp

