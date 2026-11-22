#!/bin/zsh
B=./smooth
echo "== fidelity (s=200, m=15), mean bad fraction per bundle; trace only"
for h in 2 3; do for e in 0.005 0.01 0.02 0.03 0.05 0.07 0.1 0.15 0.2 0.3 0.5 1.0; do $B embed 200 15 $h 6 $e 20 2 0; done; done
echo "== Newton on embedded instances (m=9, h=2)"
for e in 0.0 0.01 0.1 0.2 0.3 0.5 0.7 1.0; do for s in 40 160 640; do $B embed $s 9 2 6 $e 6 5 400000; done; done
echo "== Newton on smoothed j_i = max(0,i-2)"
for e in 0.0 0.1 0.3 0.5 0.7 0.9 1.0; do for n in 1024 4096 16384 65536 262144; do $B base im2 $n $e 10 11 400000; done; done
echo "== Newton on smoothed W_n"
for e in 0.01 0.1 0.3 0.5; do for n in 4096 65536; do $B base wn $n $e 10 13 400000; done; done
echo DONE
