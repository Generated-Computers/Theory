import random
def truth(j):
    x=[1]
    for i in range(1,len(j)+1): x.append(int(not(x[i-1] or x[j[i-1]])))
    return x
def newton_step(j, x):
    n=len(j); d=[0]*(n+1)
    for i in range(1,n+1):
        p,q=i-1,j[i-1]
        F=x[i]^((1^x[p])&(1^x[q]))
        s=d[p] if p==q else ((1^x[q])&d[p])^((1^x[p])&d[q])
        d[i]=F^s
    y=[x[k]^d[k] for k in range(n+1)]; y[0]=1
    return y
def trajectory(j, x0=None):
    n=len(j); xs=truth(j); x=[1]+[0]*n if x0 is None else x0[:]
    traj=[x]
    while x!=xs and len(traj)<n+5:
        x=newton_step(j,x); traj.append(x)
    return xs, traj
def strahler(j):
    # syntactic rank per Theorem Q.3: x0 constant rank 0; j_i=i-1 affine (NOT); else product of parents i-1, j_i
    n=len(j); r=[0]*(n+1)
    for i in range(1,n+1):
        p,q=i-1,j[i-1]
        if p==q: r[i]=r[p]
        else:
            a,b=sorted((r[p],r[q]),reverse=True); r[i]=a if a>b else a+1
    return r
def rand_j(n, rng=random): return [rng.randrange(i) for i in range(1,n+1)]
