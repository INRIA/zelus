include ../../config
OBJ = coffee.cmo main.cmo                                                                   
BIN = coffee                                                                                

$(BIN): $(OBJ)
	$(OCAMLC) -o $(BIN) -custom unix.cma graphics.cma $(OBJ)                            
main.ml: coffee.ml
	$(ZELUC) $(ZELUCFLAGS) -s main -sampling 0 coffee.zls                         

clean:
	/bin/rm -f *~ *.cmi *.cmo *.cmx *.o *.zci coffee.ml main.ml                   
realclean: clean
	rm -f $(BIN)                                                                        

.SUFFIXES: .zls .ml .cmo .dcc .mli .cmi .zci                                                 
.zls.ml:
	$(ZELUC) $(ZELUCFLAGS) $<                                                             
.ml.cmo:
	$(OCAMLC) -c $<                                                                     
.mli.cmi:
	$(OCAMLC) -c $<                                                                     
.mli.zci:
	$(ZELUC) $(ZELUCFLAGS) $<                                                           
#dependences                                                                                
