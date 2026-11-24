# Check: x_i = NOR(x_{i-1}, x_{i-D}) for i>=D with arbitrary first D values is periodic with period D+1 from i=2D on,
# and the polarity-gauge identities (doc #26, D.7, D.9).
import itertools, random
for D in range(1,13):
    for first in itertools.product([0,1],repeat=D):
        x=list(first)
        for i in range(D,6*D+10): x.append(1-(x[i-1]|x[i-D]))
        for i in range(2*D,len(x)-D-1): assert x[i+D+1]==x[i],(D,first,i)
        # the period-(D+1) window has no 11 and no 000 cyclically
        win=x[2*D:3*D+1]; n=len(win)
        for k in range(n):
            assert not (win[k] and win[(k+1)%n]) and not (win[k]==0 and win[(k+1)%n]==0 and win[(k+2)%n]==0)
print("lag sequence periodicity ok, D<=12")
NOR=lambda u,v:1-(u|v)
funcs={}
for a,b,c in itertools.product([0,1],repeat=3):
    tt=tuple(NOR(u^a,v^b)^c for u in (0,1) for v in (0,1)); funcs.setdefault(tt,[]).append((a,b,c))
nonaff=[tt for tt in itertools.product([0,1],repeat=4) if tt[0]^tt[1]^tt[2]^tt[3]==1]
assert set(funcs)==set(nonaff) and all(len(v)==1 for v in funcs.values())
print("unique polarity ok")
