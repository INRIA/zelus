# DS(500)
COIN_MSE_TARGET=0.001593
GAUSSIAN_MSE_TARGET=0.001337
KALMAN_MSE_TARGET=0.640335
OUTLIER_MSE_TARGET=0.933032
SLAM_MSE_TARGET=0.720609
TRACKER_MSE_TARGET=31

# # DS(1000)
# COIN_MSE_TARGET=0.001593
# GAUSSIAN_MSE_TARGET=0.001040
# KALMAN_MSE_TARGET=0.640335
# OUTLIER_MSE_TARGET=0.93
# SLAM_MSE_TARGET=0.646138
# TRACKER_MSE_TARGET=31


# DS(1)
COIN_LATENCY_TARGET=0.001000
# DS(550)
GAUSSIAN_LATENCY_TARGET=0.4710
# DS(1)
KALMAN_LATENCY_TARGET=0.001000
# DS(80)
OUTLIER_LATENCY_TARGET=0.066000
# DS(400)
SLAM_LATENCY_TARGET=1.245000
# DS(30)
TRACKER_LATENCY_TARGET=2.786000

DIRS=particles ds ds_bounded
MSE_SEARCH=../../../_build/default/examples/benchmarks/tools/mse_search.exe
LATENCY_SEARCH=../../../_build/default/examples/benchmarks/tools/latency_search.exe

all: build


mse: build \
	coin.mse \
	gaussian.mse \
	kalman.mse \
	outlier.mse \
	slam.mse \
	tracker.mse

latency: build \
	coin.latency \
	gaussian.latency \
	kalman.latency \
	outlier.latency \
	slam.latency \
	tracker.latency

build:
	dune build ./mse_search.exe

coin.mse:
	@$(foreach DIR,$(DIRS), \
		 $(MAKE) EX=coin TARGET=$(COIN_MSE_TARGET) coin_$(DIR).mse)

gaussian.mse:
	@$(foreach DIR,$(DIRS), \
		 $(MAKE) EX=gaussian TARGET=$(GAUSSIAN_MSE_TARGET) gaussian_$(DIR).mse)

kalman.mse:
	@$(foreach DIR,$(DIRS), \
		 $(MAKE) EX=kalman TARGET=$(KALMAN_MSE_TARGET) kalman_$(DIR).mse)

outlier.mse:
	@$(foreach DIR,$(DIRS), \
		 $(MAKE) EX=outlier TARGET=$(OUTLIER_MSE_TARGET) outlier_$(DIR).mse)

slam.mse:
	@$(foreach DIR,$(DIRS), \
		 $(MAKE) EX=slam TARGET=$(SLAM_MSE_TARGET) slam_$(DIR).mse)

tracker.mse:
	@$(foreach DIR,$(DIRS), \
		 $(MAKE) EX=tracker TARGET=$(TRACKER_MSE_TARGET) tracker_$(DIR).mse)

$(EX)_%.mse: ../$(EX)/%
	@$(MSE_SEARCH) -mse-target $(TARGET) $</accuracy.csv

# @$(MSE_SEARCH) -mse-target $(TARGET) ~/probabilistic/mit-ibm/ppl-zelus/papers/pldi20/eval_figures/data/coin/$</accuracy.csv

coin.latency:
	@$(foreach DIR,$(DIRS), \
		 $(MAKE) EX=coin TARGET=$(COIN_LATENCY_TARGET) coin_$(DIR).latency)

gaussian.latency:
	@$(foreach DIR,$(DIRS), \
		 $(MAKE) EX=gaussian TARGET=$(GAUSSIAN_LATENCY_TARGET) gaussian_$(DIR).latency)

kalman.latency:
	@$(foreach DIR,$(DIRS), \
		 $(MAKE) EX=kalman TARGET=$(KALMAN_LATENCY_TARGET) kalman_$(DIR).latency)

outlier.latency:
	@$(foreach DIR,$(DIRS), \
		 $(MAKE) EX=outlier TARGET=$(OUTLIER_LATENCY_TARGET) outlier_$(DIR).latency)

slam.latency:
	@$(foreach DIR,$(DIRS), \
		 $(MAKE) EX=slam TARGET=$(SLAM_LATENCY_TARGET) slam_$(DIR).latency)

tracker.latency:
	@$(foreach DIR,$(DIRS), \
		 $(MAKE) EX=tracker TARGET=$(TRACKER_LATENCY_TARGET) tracker_$(DIR).latency)

$(EX)_%.latency: ../$(EX)/%
	@$(LATENCY_SEARCH) -target $(TARGET) ~/probabilistic/mit-ibm/ppl-zelus/papers/pldi20/eval_figures/data/coin/$</accuracy.csv

# @$(LATENCY_SEARCH) -target $(TARGET) $</accuracy.csv






.phony: build coin.mse

clean:
	dune clean

cleanall: clean
	rn *~
