import itertools, math, random
def trace(j):
    x=[1]
    for i in range(1,len(j)+1):
        x.append(1-(x[i-1]|x[j[i-1]]))
    return tuple(x)
def fibn(n):
    a,b=0,1
    for _ in range(n): a,b=b,a+b
    return a
# INDEX gadget
for m in range(1,6):
    for y in itertools.product((0,1),repeat=m):
        for t in range(1,m+1):
            j=[]
            for k in range(1,m+1):
                j += [0, 0 if y[k-1]==0 else 2*k-1]
            j += [0, 2*t, 2*m+2]
            x=trace(j)
            assert all(x[2*k]==y[k-1] for k in range(1,m+1))
            assert x[2*m+1:2*m+4]==(0,1-y[t-1],y[t-1])
print("INDEX ok")
# Gamma alternating constant rows
def gamma(beta):
    H=len(beta); W=len(beta[0]) if H else 0
    def w(a,b): return 1+sum(1 for j in range(W) if len(set(beta[i][j] for i in range(a,b)))>1)
    dist=[0]*(H+1)
    for a in range(H-1,-1,-1):
        dist[a]=min(w(a,b)+dist[b] for b in range(a+1,H+1))
    return dist[0]
for H in range(1,10):
    for W in range(1,10):
        beta=[[i%2]*W for i in range(H)]
        assert gamma(beta)==min(H,W+1),(H,W,gamma(beta))
print("Gamma alt ok; H=8,W=5:",gamma([[i%2]*5 for i in range(8)]))
# Gamma <= min(H,W+1) random
for _ in range(2000):
    H=random.randint(1,7); W=random.randint(1,6)
    beta=[[random.randint(0,1) for _ in range(W)] for _ in range(H)]
    assert gamma(beta)<=min(H,W+1)
