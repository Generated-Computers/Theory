import random, math, itertools
src=open('graphchecks.py').read()
exec(src.split('# ---------- test greedy FVS')[0])
def ranks_rec(nin,preds):
    rk=[0]*nin
    for ps in preds:
        P=sorted(set(ps), key=lambda x:-rk[x])
        r1=rk[P[0]]
        rk.append(r1+1 if len(P)>1 and rk[P[1]]==r1 else r1)
    return rk
random.seed(11)
worst=0; viol=0; cnt=0
for t in range(3000):
    nin=random.randint(1,4); ng=random.randint(1,60)
    # bias towards local predecessors to create long chains/diamonds
    preds=[]
    for g in range(ng):
        k=random.choice([1,2,2,2])
        ps=[max(0,nin+g-1-int(random.expovariate(0.5))) if random.random()<0.8 else random.randrange(nin+g) for _ in range(k)]
        preds.append(ps)
    s=nin+ng
    edges=list({(min(u,nin+g),max(u,nin+g)) for g,ps in enumerate(preds) for u in set(ps)})
    H,cyc,it=greedy_fvs(s,edges)
    rk=ranks_rec(nin,preds)
    r=max(rk); h=len(H); cnt+=1
    bound=(h+1)*(math.log2(3*s)+1)
    if r>bound: viol+=1
    worst=max(worst, r/((h+1)*(math.log2(3*s)+1)))
print('instances',cnt,'violations of rank <= (h+1)(log2(3s)+1):',viol,'max ratio',round(worst,3))
