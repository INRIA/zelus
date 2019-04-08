include ../../config

OCAMLFLAGS += -I ../../lib
OCAMLOPTFLAGS += -I ../../lib
ZLEXTRALIBS = $(ZLGTKLIBS)

BASICS = counter \
				 sincefirst sincelast \
				 always always_timed \
				 once once_timed \
			   onceBfromlastA onceBfromfirstA \
			   alwaysBfromlastA alwaysBfromfirstA \
			   onceBfromlastA_timed onceBfromfirstA_timed \
			   alwaysBfromlastA_timed alwaysBfromfirstA_timed \
				 onceBfromlastAtoC onceBfromfirstAtoC \
				 alwaysBfromlastAtoC alwaysBfromfirstAtoC

TEMPLATES = absence absence_timed minimum_duration maximum_duration \
			 			bounded_recurrence bounded_response bounded_invariance

default: $(word 1, $(targets))
all:  $(targets)
byte: basics_byte templates_byte
opt: basics_opt templates_opt

templates: templates_byte
templates_byte: $(TEMPLATES:=.byte)
templates_opt: $(TEMPLATES:=.opt)

basics: basics_byte
basics_byte: $(BASICS:=.byte)
basics_opt: $(BASICS:=.opt)

basic_obs.ml: basic_obs.zls
	$(ZELUC) $(ZELUCFLAGS) $(ZELUCEXTRAFLAGS) $<

$(BASICS:=.ml): basic_obs.zls
	$(ZELUC) $(ZELUCFLAGS) $(ZELUCEXTRAFLAGS) -gtk2 -s $(@:%.ml=test_%) \
					 -o $(@:.ml=) $<

$(BASICS:=.byte): basic_obs.ml
	$(MAKE) $(@:.byte=.ml)
	$(OCAMLC) $(OCAMLFLAGS) -o $@ \
	    $(ZLSTDLIBS) $(ZLEXTRALIBS) $(INCLUDES) \
			$< $(@:.byte=.ml)

$(BASICS:=.opt): basic_obs.ml
	$(MAKE) $(@:.opt=.ml)
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ \
	    $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) \
			$(INCLUDES:.cma=.cmxa) $< $(@:.opt=.ml)

pattern_templates.ml: pattern_templates.zls
	$(ZELUC) $(ZELUCFLAGS) $(ZELUCEXTRAFLAGS) $<

$(TEMPLATES:=.ml): pattern_templates.zls
	$(ZELUC) $(ZELUCFLAGS) $(ZELUCEXTRAFLAGS) -gtk2 -s $(@:%.ml=test_%) \
					 -o $(@:.ml=) $<

$(TEMPLATES:=.byte): pattern_templates.ml
	$(MAKE) $(@:.byte=.ml)
	$(OCAMLC) $(OCAMLFLAGS) -o $@ \
	    $(ZLSTDLIBS) $(ZLEXTRALIBS) $(INCLUDES) \
			$< $(@:.byte=.ml)

$(TEMPLATES:=.opt): pattern_templates.ml
	$(MAKE) $(@:.opt=.ml)
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ \
	    $(ZLSTDLIBS:.cma=.cmxa) $(ZLEXTRALIBS:.cma=.cmxa) \
			$(INCLUDES:.cma=.cmxa) $< $(@:.opt=.ml)

clean:
	-@rm -f pattern_templates.ml pattern_templates_main.ml $(TEMPLATES:=.ml)
	-@rm -f basics_obs.ml basics_obs_main.ml $(BASICS:=.ml)
	-@rm -f *.o *.cm[oix] *.annot *.obc *.zci

realclean cleanall: clean
	-@rm -f *.byte *.opt
