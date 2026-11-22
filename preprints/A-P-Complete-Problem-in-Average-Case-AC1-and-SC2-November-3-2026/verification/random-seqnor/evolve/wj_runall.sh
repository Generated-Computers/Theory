#!/bin/sh
# NOTE.md §5j findings 10-11: windowed Jacobi (wjacobi.c) and coalescence of block bases (coupling.c).
# usage: sh wj_runall.sh TB6DIR > results/wjacobi.out   (TB6DIR made by gen_big.py, see its usage line;
#        needs ./wjacobi and ./coupling built with cc -O2)
TB=$1
echo "# block bases of Table tab:block (B = 32, h = 4), windows L = LB = 256 and 1024"
for e in 0 0.1 0.3; do for n in 262144 1048576 4194304; do for W in 256 1024; do
  ./wjacobi $W $W 20000 bb $n 32 4 $e 2 23; done; done; done
echo "# longer blocks (h = B/8), windows 1024 and 4096"
for B in 64 128 256; do for e in 0 0.1 0.3 0.5; do for n in 1048576 2097152; do for W in 1024 4096; do
  ./wjacobi $W $W 6000 bb $n $B $((B/8)) $e 2 23; done; done; done; done
echo "# test bed, windows 1024"
for f in "$TB"/*.bin; do ./wjacobi 1024 1024 600 file "$f"; done
echo "# coalescence at eps = 0 and 0.1 (64 copies, 40 trials, cap 4000 blocks)"
for e in 0 0.1; do for B in 8 12 16 20 24 28 32 40 48 64 128 256 512 1024; do
  ./coupling $B $((B/8>2?B/8:2)) $e 4000 40 7; done; done
echo "# first agreement under noise (20 trials, cap 1000 blocks)"
for B in 128 512 2048; do for e in 0.1 0.2 0.25 0.3 0.35 0.4 0.5; do ./coupling $B $((B/8)) $e 1000 20 11; done; done
echo "# profiles against the true trace at eps = 0"
for B in 32 128 512; do ./coupling $B $((B/8)) 0 8192 12 3 profile; done
