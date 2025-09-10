#!/usr/bin/env gnuplot

if (!exists("options")) options = "clutch.out"

set terminal postscript font ",4";

set xlabel "t (seconds)";
set key autotitle columnhead;

set multiplot title (sprintf("Clutch model (%s)", options)) layout 2,1;
set lmargin 10;

set xlabel 'Time';
set key top right;

set title 'Inputs';
set ylabel 'Engine torque and Frictions from Clutch Normal Force';
set yrange [0:2.1];

set xtics 2;
set grid;

set key autotitles columnhead;

set ytics 0.5;
plot "clutch.out" using 1:2 with lines, \
               '' using 1:3 with lines, \
               '' using 1:4 with lines;

set title 'Outputs';
set ylabel 'Engine, Vehicle and Shaft speeds';
set yrange [0:0.8];
set ytics 0.1;
plot "clutch.out" using 1:5 with lines, \
               '' using 1:6 with lines, \
               '' using 1:7 with lines;

