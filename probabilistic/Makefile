all:
	$(MAKE) -C owl
	$(MAKE) -C inference
	$(MAKE) -C examples

clean:
	$(MAKE) -C owl clean
	$(MAKE) -C inference clean
	$(MAKE) -C examples clean

cleanall:
	-rm -f *~
	$(MAKE) -C owl cleanall
	$(MAKE) -C inference cleanall
	$(MAKE) -C examples cleanall
