
all: runverbatim.sty runverbatim.pdf

runverbatim.pdf: runverbatim.dtx runverbatim.ind runverbatim.sty runverbatim.rvrb
	./runverbatim.sh
	pdflatex $<
	pdflatex $<
	@printf "\n\n"
	# TODO: find a way to extract important logged messages
	#-@rubber-info $<

runverbatim.ind: runverbatim.idx
	makeindex -s gind.ist -o $@ $<

runverbatim.idx runverbatim.rvrb: runverbatim.dtx
	pdflatex $<

runverbatim.sty:
	latex runverbatim.ins

clean:
	-@rm -rf runverbatim0*.tex runverbatim0*.ml Withopen*
	-@rm -rf runverbatim.aux runverbatim.glo runverbatim.idx
	-@rm -rf runverbatim.ilg runverbatim.ind runverbatim.log
	-@rm -rf runverbatim.rvrb runverbatim.tmp

