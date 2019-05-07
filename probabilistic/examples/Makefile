all:
	$(MAKE) -C gridworld
	$(MAKE) -C coin
	echo "Ignore:" $(MAKE) -C heater
	$(MAKE) -C hiking
	$(MAKE) -C hmm
	$(MAKE) -C ilmdp
	$(MAKE) -C line
	$(MAKE) -C pid
	$(MAKE) -C restaurants
	$(MAKE) -C gaussian_gaussian
	$(MAKE) -C beta_bernoulli
	$(MAKE) -C slam
	$(MAKE) -C walker

clean:
	$(MAKE) -C gridworld clean
	$(MAKE) -C coin clean
	$(MAKE) -C heater clean
	$(MAKE) -C hiking clean
	$(MAKE) -C hmm clean
	$(MAKE) -C ilmdp clean
	$(MAKE) -C line clean
	$(MAKE) -C pid clean
	$(MAKE) -C restaurants clean
	$(MAKE) -C gaussian_gaussian clean
	$(MAKE) -C beta_bernoulli clean
	$(MAKE) -C slam clean
	$(MAKE) -C walker clean

realclean cleanall:
	$(MAKE) -C gridworld cleanall
	$(MAKE) -C coin cleanall
	$(MAKE) -C heater cleanall
	$(MAKE) -C hiking cleanall
	$(MAKE) -C hmm cleanall
	$(MAKE) -C ilmdp cleanall
	$(MAKE) -C line cleanall
	$(MAKE) -C pid cleanall
	$(MAKE) -C restaurants cleanall
	$(MAKE) -C gaussian_gaussian cleanall
	$(MAKE) -C beta_bernoulli cleanall
	$(MAKE) -C slam cleanall
	$(MAKE) -C walker cleanall
	-rm -f *~
