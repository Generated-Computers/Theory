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
# census and fibers
for N in range(1,9):
    fib={}
    for j in itertools.product(*[range(i) for i in range(1,N+1)]):
        fib.setdefault(trace(j),[]).append(j)
    assert len(fib)==fibn(N+1), (N,len(fib))
    for x,js in fib.items():
        c=[]
        for i in range(1,N+1):
            A=[jj for jj in range(i) if 1-(x[i-1]|x[jj])==x[i]]
            c.append(len(A))
            # formula
            if x[i-1]==1: assert len(A)==i
            elif x[i]==1: assert len(A)==sum(1 for t in x[:i] if t==0)
            else: assert len(A)==sum(1 for t in x[:i] if t==1)
        assert len(js)==math.prod(c)
        assert set(js)==set(itertools.product(*[[jj for jj in range(i) if 1-(x[i-1]|x[jj])==x[i]] for i in range(1,N+1)]))
    # K_{N,q}
    Ks=[]
    for q in range(0,N+1):
        K=0; Cmax=0
        for x in fib:
            c=sorted([sum(1 for jj in range(i) if 1-(x[i-1]|x[jj])==x[i]) for i in range(1,N+1)],reverse=True)
            C=math.prod(c[:q]); K+=C; Cmax=max(Cmax,C)
        Ks.append(K)
        falling=math.prod(range(N-q+1,N+1))
        lo=fibn(N+1)*N**q*(1-3*q*(q+1)/N)
        assert K<=fibn(N+1)*falling and K>=lo-1e-9, (N,q,K)
        assert Cmax<=falling and Cmax>=N**q*(1-3*q*(q+1)/N)-1e-9
    print("N",N,"traces",len(fib),"K_{N,q}",Ks, "N!",math.factorial(N))
