#!/bin/sh
# Reproduces Tables tab:kpr and tab:kpr-greedy and the near-threshold scan. Output: kpr_runall.out
cc -O2 -o kp_probe kp_probe.c -lm && cc -O2 -o kp_greedy kp_greedy.c -lm || exit 1
{
echo "# KP (kp) vs relevance variant (kprd) vs Newton; mean/max rounds over 3 smoothings, seed 1"
for f in spread64 log lgu im2; do for e in 0.5 0.6; do
  for L in 12 16 20; do ./kp_probe kp $f $((1<<L)) $e 3 1; ./kp_probe kprd $f $((1<<L)) $e 3 1; done
  ./kp_probe newton $f $((1<<20)) $e 3 1 5000
done; done
echo "# greedy adversarial bases: built against the algorithm named, trained on 24 smoothings, tested on 6 fresh ones"
for e in 0.5 0.6 0.7; do for L in 12 14 16; do ./kp_greedy kp $((1<<L)) $e 24 6 11; ./kp_greedy kpr $((1<<L)) $e 24 6 11; done; done
echo "# relevance variant near its empirical threshold, spread bases, 3 smoothings, seed 4"
for f in spread16 spread64 spread256 spread1024; do for e in 0.4 0.45 0.5 0.55; do for L in 14 18 22; do
  ./kp_probe kprd $f $((1<<L)) $e 3 4; done; done; done
echo "# cross-check: direct simulation of the relevance-pruned iteration (kpr) against the O(n) depth (kprd)"
for f in spread64 log lgu im2; do for e in 0.5 0.6; do for L in 12 16; do
  a=$(./kp_probe kpr $f $((1<<L)) $e 3 1 | awk '{print $5, $6}'); b=$(./kp_probe kprd $f $((1<<L)) $e 3 1 | awk '{print $5, $6}')
  [ "$a" = "$b" ] && echo "agree $f eps=$e n=2^$L $a" || echo "MISMATCH $f eps=$e n=2^$L sim=$a depth=$b"
done; done; done
} > kpr_runall.out 2>&1
