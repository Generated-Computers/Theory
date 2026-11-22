#!/bin/sh
# Reproduces Table tab:kpr-relax and the fixed-distance runs of Appendix A. Output: kpr_relax.out
cc -O2 -o kpr_relax kpr_relax.c -lm && cc -O2 -o kp_probe kp_probe.c -lm || exit 1
{
echo "# max over positions of four depths, mean over 2 smoothings, seed 3"
for f in spread16 spread64 spread256 lgu; do for e in 0.6 0.7 0.8; do for L in 14 18 22 24; do
  ./kpr_relax $f $((1<<L)) $e 2 3; done; done; done
echo "# relevance-pruned iteration on fixed-distance bases j_i = i - C, 3 smoothings, seed 1"
for C in 3 4 5 6 8 10 16 32; do for L in 12 16 20; do ./kp_probe kprd fix$C $((1<<L)) 0.6 3 1; done; done
for e in 0.6 0.55 0.5; do for L in 14 18 22 24; do ./kp_probe kprd fix4 $((1<<L)) $e 2 2; done; done
} > kpr_relax.out 2>&1
rm -f kpr_relax kp_probe
