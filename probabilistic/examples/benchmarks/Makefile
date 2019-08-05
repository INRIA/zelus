all:
	$(MAKE) -C harness
	$(MAKE) -C coin
	$(MAKE) -C kalman
	$(MAKE) -C outlier

bench:
	$(MAKE) -C coin bench
	$(MAKE) -C kalman bench
	$(MAKE) -C outlier bench

publish:
	$(MAKE) -C coin publish
	$(MAKE) -C kalman publish
	$(MAKE) -C outlier publish

clean:
	$(MAKE) -C harness clean
	$(MAKE) -C coin clean
	$(MAKE) -C kalman clean
	$(MAKE) -C outlier clean

realclean cleanall:
	$(MAKE) -C harness cleanall
	$(MAKE) -C coin cleanall
	$(MAKE) -C kalman cleanall
	$(MAKE) -C outlier cleanall
	-rm -f *~
