
OBJ=backhoe.pdf

$(OBJ): $(OBJ:.pdf=.tex) $(OBJ:.pdf=.bib)
	pdflatex $(OBJ:.pdf=)
	bibtex $(OBJ:.pdf=)
	pdflatex $(OBJ:.pdf=)
	pdflatex $(OBJ:.pdf=)

clean:
	@-rm -f $(OBJ:.pdf=.aux) $(OBJ:.pdf=.aux) $(OBJ:.pdf=.log) $(OBJ:.pdf=.out)
	@-rm -f $(OBJ:.pdf=.bbl) $(OBJ:.pdf=.blg)

cleanall: realclean
realclean:
	@-rm -f $(OBJ)

