
OBJ=slides.pdf

$(OBJ): $(OBJ:.pdf=.tex) simulink.pdf simulink-nohit.pdf simulink-zoom.pdf zelus.pdf zelus-zoom.pdf
	pdflatex $(OBJ:.pdf=)
	pdflatex $(OBJ:.pdf=)

simulink.pdf simulink-zoom.pdf simulink-nohit.pdf zelus.pdf zelus-zoom.pdf: simulink.log simulink-nohit.log zelus.log

clean:
	@-rm -f $(OBJ:.pdf=.aux) $(OBJ:.pdf=.aux) $(OBJ:.pdf=.log) $(OBJ:.pdf=.out)
	@-rm -f $(OBJ:.pdf=.bbl) $(OBJ:.pdf=.blg)
	@-rm -f $(OBJ:.pdf=.nav) $(OBJ:.pdf=.snm) $(OBJ:.pdf=.toc)

cleanall: realclean
realclean: clean
	@-rm -f $(OBJ)

