#!/bin/sh
# Where does the relevance-pruned iteration stop being logarithmic? Output: kpr_edge.out
cc -O2 -o kp_probe kp_probe.c -lm && cc -O2 -o kp_greedy kp_greedy.c -lm || exit 1
{
echo "# KPR (O(n) depth) on spread, log-uniform and fixed-distance bases, n = 2^16..2^26, 2 smoothings, seed 9"
for f in spread64 spread256 lgu fix4; do for e in 0.45 0.50 0.55; do for L in 16 20 24 26; do
  ./kp_probe kprd $f $((1<<L)) $e 2 9; done; done; done
echo "# greedy bases against KPR, 24 training / 6 fresh smoothings, seed 13"
for e in 0.45 0.50 0.55; do for L in 12 14 16 18; do ./kp_greedy kpr $((1<<L)) $e 24 6 13; done; done
} > kpr_edge.out 2>&1
rm -f kp_probe kp_greedy
