
OBJ=slides.pdf

$(OBJ): $(OBJ:.pdf=.tex)
	pdflatex $(OBJ:.pdf=)
	pdflatex $(OBJ:.pdf=)

clean:
	@-rm -f $(OBJ:.pdf=.aux) $(OBJ:.pdf=.aux) $(OBJ:.pdf=.log) $(OBJ:.pdf=.out)
	@-rm -f $(OBJ:.pdf=.bbl) $(OBJ:.pdf=.blg)
	@-rm -f $(OBJ:.pdf=.nav) $(OBJ:.pdf=.snm) $(OBJ:.pdf=.toc)

cleanall: realclean
realclean: clean
	@-rm -f $(OBJ)

