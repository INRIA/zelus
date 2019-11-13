COIN_TARGET=0.0016
GAUSSIAN_TARGET=0.001
KALMAN_TARGET=0.64
OUTLIER_TARGET=0.93
SLAM_TARGET=0.72
TRACKER_TARGET=32

DIRS=particles ds ds_bounded
MSE_SEARCH=../../../_build/default/examples/benchmarks/tools/mse_search.exe

all: build

mse: build \
	coin.mse \
	gaussian.mse \
	kalman.mse \
	outlier.mse \
	slam.mse \
	tracker.mse

build:
	dune build ./mse_search.exe

coin.mse:
	@$(foreach DIR,$(DIRS), \
		 $(MAKE) EX=coin TARGET=$(COIN_TARGET) coin_$(DIR).mse)

gaussian.mse:
	@$(foreach DIR,$(DIRS), \
		 $(MAKE) EX=gaussian TARGET=$(GAUSSIAN_TARGET) gaussian_$(DIR).mse)

kalman.mse:
	@$(foreach DIR,$(DIRS), \
		 $(MAKE) EX=kalman TARGET=$(KALMAN_TARGET) kalman_$(DIR).mse)

outlier.mse:
	@$(foreach DIR,$(DIRS), \
		 $(MAKE) EX=outlier TARGET=$(OUTLIER_TARGET) outlier_$(DIR).mse)

slam.mse:
	@$(foreach DIR,$(DIRS), \
		 $(MAKE) EX=slam TARGET=$(SLAM_TARGET) slam_$(DIR).mse)

tracker.mse:
	@$(foreach DIR,$(DIRS), \
		 $(MAKE) EX=tracker TARGET=$(TRACKER_TARGET) tracker_$(DIR).mse)

$(EX)_%.mse: ../$(EX)/%
	@$(MSE_SEARCH) -mse-target $(TARGET) $</accuracy.csv



.phony: build coin.mse

clean:
	dune clean

cleanall: clean
	rn *~
