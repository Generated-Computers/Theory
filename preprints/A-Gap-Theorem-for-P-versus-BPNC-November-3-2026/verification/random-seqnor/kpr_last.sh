#!/bin/sh
# Growth of the last-reset relaxation D_last between 0.686 and 3/4 (Remark rem:kpr, Appendix A). Output: kpr_last.out
cc -O2 -o kpr_relax kpr_relax.c -lm && cc -O2 -o kp_greedy kp_greedy.c -lm || exit 1
{
echo "# max depths, mean over 2 smoothings, seed 5"
for f in spread64 spread256 lgu; do for e in 0.70 0.73; do for L in 16 20 24 26; do
  ./kpr_relax $f $((1<<L)) $e 2 5; done; done; done
echo "# greedy bases built against D_last (24 training smoothings, 6 fresh)"
for e in 0.70 0.73 0.80; do for L in 12 14 16 18; do ./kp_greedy last $((1<<L)) $e 24 6 11; done; done
} > kpr_last.out 2>&1
rm -f kpr_relax kp_greedy
