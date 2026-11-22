import sys, subprocess
sys.path.insert(0, sys.argv[1]); from core import *
M64=(1<<64)-1
def splitmix(seed):
    s=seed
    while True:
        s=(s+0x9e3779b97f4a7c15)&M64; z=s
        z=((z^(z>>30))*0xbf58476d1ce4e5b9)&M64; z=((z^(z>>27))*0x94d049bb133111eb)&M64
        yield z^(z>>31)
for seed in (11,12,13):
    n=3000; g=splitmix(seed); j=[(next(g)*i)>>64 for i in range(1,n+1)]
    xs,tr=trajectory(j)
    py=[ [i for i in range(n+1) if x[i]!=xs[i]][0] for x in tr[:-1] ]
    out=subprocess.run([sys.argv[1]+"/newton",str(n),str(seed)],capture_output=True,text=True).stdout.split("\n")
    c=[int(l.split()[1]) for l in out if l and not l.startswith("#")]
    print(seed, "python fronts", py); print(seed, "C      fronts", c, "MATCH" if py==c else "MISMATCH")
