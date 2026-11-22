#!/bin/zsh
# KP iteration experiments behind paper Table (tab:kp); build: cc -O2 smooth.c -o smooth -lm
B=${B:-./smooth}
echo "== KP on uniform instances"
for n in 1024 16384 262144 4194304; do $B base unif $n 1.0 10 1 100000 kp; done
echo "== KP on smoothed bases"
for f in im2 im3 wn one half sqrt; do for e in 0.5 0.7 0.8 0.9; do for n in 4096 65536 1048576; do $B base $f $n $e 6 3 400000 kp; done; done; done
echo "== KP on embedded instances (m=9, h=2)"
for e in 0.0 0.01 0.3 0.6 0.8 0.9 1.0; do for s in 40 160 640; do $B embed $s 9 2 6 $e 4 5 400000 kp; done; done
echo DONE
