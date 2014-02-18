include ../../../config

COLTITLES="Tin,Tfmaxs,Tfmaxk,Engine,Vehicle,Shaft"
RUNS=ode23.out ode45.out ode3.out

all: $(RUNS:.out=.pdf)

%.out: %_in.mat %_out.mat
	$(TOOLS)/mat_to_text --titles $(COLTITLES) \
	    $(@:.out=_in.mat) $(@:.out=_out.mat) > $@

%.pdf: %.out
	./plot_clutch $< > $@

