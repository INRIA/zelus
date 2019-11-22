if (!exists("ex")) ex='coin'
dir='../'.ex.'/'


set datafile separator comma
set key autotitle columnhead samplen 2

set terminal png
set output ex.'-perf-step.png'

set xlabel 'Step'
set logscale y
set ylabel 'Step latency (ms, log scale)'

set title ex.': Performance per step'

plot dir.'particles/perf-step.csv' using 1:3:2:4 every 40 with yerrorbars lt 3 pt 5 title 'PF', \
     dir.'ds_bounded/perf-step.csv' using 1:3:2:4 every 40 with yerrorbars lt 4 pt 7 title 'BDS', \
     dir.'ds/perf-step.csv' using 1:3:2:4 every 40 with yerrorbars lt 1 pt 11 title 'SDS', \
     dir.'ds_nogc/perf-step.csv' using 1:3:2:4 every 40 with yerrorbars lt 2 pt 9 title 'DS'
