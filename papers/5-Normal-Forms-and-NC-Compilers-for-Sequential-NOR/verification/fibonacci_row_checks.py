import itertools
def fib_words(W):
    return [w for w in itertools.product((0,1),repeat=W) if all(not(w[j] and w[j+1]) for j in range(W-1))]
def row(B,L,x):
    y=[]; prev=L
    for j in range(len(x)):
        v=(1-prev)&(x[j]^B[j]); y.append(v); prev=v
    return tuple(y)
def fibn(n):
    a,b=0,1
    for _ in range(n): a,b=b,a+b
    return a
bad=0
for W in range(1,11):
    FW=fib_words(W); FWs=set(FW)
    allB=list(itertools.product((0,1),repeat=W))
    stable_count=0; inj=[]
    minimg=None
    for B in allB:
        for L in (0,1):
            f={x:row(B,L,x) for x in FW}
            st=all(f[f[f[x]]]==f[x] for x in FW)
            # criterion
            word = B[:W-1] if L==0 else B[1:W-1]
            crit = all(not(word[j] and word[j+1]) for j in range(len(word)-1))
            if W>=2 and st!=crit: bad+=1
            stable_count+=st
            if len(set(f.values()))==len(FW): inj.append((B,L))
            if L==0 and B in FWs:
                if not st: bad+=1
                img=len(set(f.values()))
                minimg=img if minimg is None else min(minimg,img)
                if img < 2**((W+1)//2): bad+=1
    expected = 2*fibn(W+1)+4*fibn(W) if W>=2 else 4
    if stable_count!=expected: print("count mismatch",W,stable_count,expected); bad+=1
    expinj={(tuple([0]*W),0),(tuple([0]*(W-1)+[1]),0)}
    if set(inj)!=expinj: print("inj mismatch",W,inj); bad+=1
    print("W",W,"min image (Fib B, L=0)",minimg,"2^ceil(W/2)",2**((W+1)//2),"stable",stable_count)
# rank recurrence
def rho(B):
    W=len(B); FW=fib_words(W)
    return len(set(row(B,0,x) for x in FW))
for W in range(2,11):
    for B in fib_words(W):
        r=rho(B)
        if B[0]==1: rr=2*rho(B[2:])
        else: rr=rho(B[1:])+rho(B[2:])
        if r!=rr: bad+=1
print("rho eps",rho(()),"rho(0)",rho((0,)),"rho(1)",rho((1,)))
# atom factorization and fibre bound
for W in range(1,9):
    FW=fib_words(W)
    def E(i):
        B=tuple(1 if t==i else 0 for t in range(W)); return lambda x: row(B,0,x)
    R=lambda x: row(tuple([0]*W),1,x)
    for i in range(W):
        f=E(i); fib={}
        for x in FW: fib.setdefault(f(x),[]).append(x)
        if max(len(v) for v in fib.values())>2: bad+=1
    fib={}
    for x in FW: fib.setdefault(R(x),[]).append(x)
    if max(len(v) for v in fib.values())>2: bad+=1
    for B in itertools.product((0,1),repeat=W):
        for L in (0,1):
            for x in FW:
                y=x if L==0 else R(x)
                start = 0 if L==0 else 1
                for i in range(start,W):
                    if B[i]: y=E(i)(y)
                if L==0 and B[0]==0: pass
                if y!=row(B,L,x): bad+=1
print("V204 violations",bad)
# image of T_C o T_A with A=0101.., C=1010.. (1-indexed b1 b2..): A: b_j = 1 iff j even; C: b_j=1 iff j odd
for W in range(1,13):
    FW=fib_words(W)
    A=tuple(1 if (j+1)%2==0 else 0 for j in range(W)); C=tuple(1 if (j+1)%2==1 else 0 for j in range(W))
    I=tuple([0]*W)
    img=set(row(C,0,row(A,0,x)) for x in FW)
    img2=set(row(A,0,row(C,0,x)) for x in FW)
    print(W,"|T_C T_A(F)|",len(img),"|T_A T_C(F)|",len(img2),"ceil(W/2)+1",(W+1)//2+1, "rhoA",rho(A),"rhoC",rho(C))
# constant two-row block S = (1010..., west 0), (1^W, west 1)
for W in range(1,13):
    FW=fib_words(W)
    C=tuple(1 if (j+1)%2==1 else 0 for j in range(W)); One=tuple([1]*W)
    img=set(row(One,1,row(C,0,x)) for x in FW)
    assert img=={tuple(1 if (j+1)%2==0 else 0 for j in range(W))}, W
print("two-row block S has constant image for W<=12")
