#!/usr/bin/gnuplot

#
# Usage: ./plotTacticTimingData.gnuplot tacticTiming.dat
#

set terminal pngcairo  transparent enhanced font "arial,10" fontscale 2.0 size 2400, 1600
set output 'histograms.2.png'
set boxwidth 0.9 absolute
set style fill   solid 1.00 border lt -1
#set key fixed right top vertical Right noreverse noenhanced autotitle nobox
set style increment default
set style histogram clustered gap 1 title textcolor lt -1
set datafile missing '-'
set style data histograms
set xtics border in scale 0,0 nomirror rotate by -45  autojustify
set xtics  norangelimit 
set xtics   ()
set title "Cogent Type Tactics Timing" 
set xrange [ * : * ] noreverse writeback
set x2range [ * : * ] noreverse writeback
set yrange [ * : * ] noreverse writeback
set y2range [ * : * ] noreverse writeback
set zrange [ * : * ] noreverse writeback
set cbrange [ * : * ] noreverse writeback
set rrange [ * : * ] noreverse writeback

set ylabel "time (μs)"
## Last datafile plotted: "immigration.dat"
plot 'tacticTiming.dat' using 2:xtic(1) ti col, '' u 3 ti col, '' u 4 ti col, '' u 5 ti col, '' u 6 ti col, '' u 7 ti col, '' u 8 ti col
