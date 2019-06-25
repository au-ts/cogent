#!/usr/bin/gnuplot

#
# Copyright 2018, Data61
# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
# ABN 41 687 119 230.
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(DATA61_GPL)
#

#
# Usage: ./plotTacticTimingData.gnuplot
# Must have a datafile called 'tacticTiming.dat' in the same directory
# Script modified from original located here: http://gnuplot.sourceforge.net/demo/histograms.2.gnu
#


set terminal pngcairo  transparent enhanced font "arial,10" fontscale 2.0 size 2400, 1600
set output 'histograms.2.png'
set boxwidth 0.9 absolute
set style fill   solid 1.00 border lt -1
#set key fixed right top vertical Right noreverse noenhanced autotitle nobox
set style increment default
set style histogram clustered gap 6 title textcolor lt -1
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
set logscale y 10

# file must be called 'tacticTiming.dat'
plot 'tacticTiming.dat' using 2:xtic(1) ti col, '' u 3 ti col, '' u 4 ti col, '' u 5 ti col, '' u 6 ti col, '' u 7 ti col, '' u 8 ti col
