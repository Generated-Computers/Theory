#!/bin/sh
# Table tab:block: random block bases, blocks of length 32 and 128, h = 4, 4 smoothings each.
# usage: sh nogo_block.sh > nogo_block.out   (needs blockbase compiled as ./bb)
BB=${BB:-./bb}
for e in 0.3 0.4 0.45 0.5 0.55 0.6 0.65; do
  for B in 32 128; do
    for n in 262144 1048576 4194304 16777216; do $BB $n $B 4 $e 4 23; done
  done
done
