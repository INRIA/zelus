all:
	$(MAKE) -C harness
	$(MAKE) -C coin
	$(MAKE) -C kalman
	$(MAKE) -C outlier
	$(MAKE) -C slam

bench:
	$(MAKE) -C coin bench
	$(MAKE) -C kalman bench
	$(MAKE) -C outlier bench
	$(MAKE) -C slam bench

bench_per_particles:
	$(MAKE) -C coin bench_per_particles
	$(MAKE) -C kalman bench_per_particles
	$(MAKE) -C outlier bench_per_particles
	$(MAKE) -C slam bench_per_particles

bench_per_steps:
	$(MAKE) -C coin bench_per_steps
	$(MAKE) -C kalman bench_per_steps
	$(MAKE) -C outlier bench_per_steps
	$(MAKE) -C slam bench_per_steps

bench_mem_ideal:
	$(MAKE) -C coin bench_mem_ideal
	$(MAKE) -C kalman bench_mem_ideal
	$(MAKE) -C outlier bench_mem_ideal
	$(MAKE) -C slam bench_mem_ideal

publish:
	$(MAKE) -C coin publish
	$(MAKE) -C kalman publish
	$(MAKE) -C outlier publish
	$(MAKE) -C slam publish

clean:
	$(MAKE) -C harness clean
	$(MAKE) -C coin clean
	$(MAKE) -C kalman clean
	$(MAKE) -C outlier clean
	$(MAKE) -C slam clean

realclean cleanall:
	-rm -f *~
	$(MAKE) -C harness cleanall
	$(MAKE) -C coin cleanall
	$(MAKE) -C kalman cleanall
	$(MAKE) -C outlier cleanall
	$(MAKE) -C slam cleanall
