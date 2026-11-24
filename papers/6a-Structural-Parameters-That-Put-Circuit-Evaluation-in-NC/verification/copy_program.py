# Copy program of Prop. 5.1 in manuscript 010a: exact machine, rank, rounds of the table iteration.
BOT=None
def check(d,N):
    m=d; Hin=[1]*d
    p=lambda c: (c[0]) if c[0]+1<=d else c[0]+1   # c=(t-1,v): t-1 if t<=d else t
    w=lambda c: c[1]
    phi=lambda t,c,h: (t,h)
    wr=lambda s: m+s-1
    def read(t,a,Z):
        if 0<=a<m: return Hin[a],None
        s=a-m+1
        if 1<=s<t: return w(Z[s-1]),s
        return BOT,None
    C=[(0,1)]; writers=[None]
    for t in range(1,N+1):
        h,s=read(t,p(C[t-1]),C); writers.append(s); C.append(phi(t,C[t-1],h))
    assert all(c[1]==1 for c in C)
    a=[0]*(N+1)
    for t in range(1,N+1):
        a[t]=a[t-1] if writers[t] is None else max(a[t-1],1+a[writers[t]-1])
    assert all(a[t]==(t-1)//d for t in range(1,N+1))
    Z=[(0,1)]+[(t,0) for t in range(1,N+1)]; r=0
    while Z!=C:
        Zn=[(0,1)]
        for t in range(1,N+1):
            h,_=read(t,p(Zn[t-1]),Z); Zn.append(phi(t,Zn[t-1],h))
        Z=Zn; r+=1
        assert all((Z[t][1]==1)==(t<=r*d) for t in range(1,N+1))
    assert r==max(a)+1==-(-N//d), (d,N,r,max(a))
for d in range(2,7):
    for N in range(1,60): check(d,N)
print("copy program ok")
