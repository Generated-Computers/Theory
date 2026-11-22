# Large test bed for windowed Jacobi (NOTE.md §5j, wj_runall.sh): the families of gen_testbed.py at
# seed 1, written in the same format.
# usage: python3 -I gen_big.py OUTDIR fam1,fam2,... size1,size2,...
#   e.g. python3 -I gen_big.py tb6 block8,emb-rand,emb-w2,emb-w8,emb-wsqrt,emb1-w8,lin2,remb-w8,rev-w8,uniform 65536,262144,1048576
import os, random, struct, sys, zlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_testbed import family
out = sys.argv[1]; os.makedirs(out, exist_ok=True)
fams = sys.argv[2].split(','); sizes = [int(s) for s in sys.argv[3].split(',')]
for f in fams:
    for size in sizes:
        rng = random.Random(zlib.crc32(('%d/%s/%d' % (1, f, size)).encode()))
        j = family(f, size, rng)
        with open(os.path.join(out, '%s_%d.bin' % (f, size)), 'wb') as fh:
            fh.write(struct.pack('<i', len(j))); fh.write(struct.pack('<%di' % len(j), *j))
        print(f, size, len(j), flush=True)
