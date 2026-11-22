# Randomized check of global table iteration (doc #26, Thm O.2) on random append-read machines.
import random
BOT='bot'
def make_machine(rng, nstates, nwords, m):
    # local states 0..nstates-1 ; words 0..nwords-1 ; addresses 0..m+N
    p={c: rng.randrange(0, 3*m+5) for c in range(nstates)}   # read address (absolute)
    w={c: rng.randrange(nwords) for c in range(nstates)}
    Phi={}
    def phi(t,c,h):
        key=(t%3,c,h)
        if key not in Phi: Phi[key]=rng.randrange(nstates)
        return Phi[key]
    return p,w,phi
def run(machine,Hin,C0,N):
    p,w,phi=machine; m=len(Hin); C=[C0]; writer=[]  # wr(s)=m+s-1 for s>=1
    reads=[None]
    for t in range(1,N+1):
        a=p[C[t-1]]
        if a<m: h=Hin[a]; src=('init',)
        elif m<=a<m+t-1: s=a-m+1; h=w[C[s-1]]; src=('int',s)
        else: h=BOT; src=('inv',)
        reads.append(src); C.append(phi(t,C[t-1],h))
    return C,reads
def H(machine,Hin,Z,N):
    p,w,phi=machine; m=len(Hin); out=[Z[0]]
    for t in range(1,N+1):
        c=out[t-1]; a=p[c]
        if a<m: h=Hin[a]
        elif m<=a<m+t-1: s=a-m+1; h=w[Z[s-1]]
        else: h=BOT
        out.append(phi(t,c,h))
    return out
def rank(reads,N):
    a=[0]*(N+1)
    for t in range(1,N+1):
        if reads[t][0]=='int': a[t]=max(a[t-1],1+a[reads[t][1]-1])
        else: a[t]=a[t-1]
    return a
rng=random.Random(1)
worst=0; trials=0
for trial in range(3000):
    ns=rng.randrange(2,7); nw=rng.randrange(1,4); m=rng.randrange(1,5); N=rng.randrange(1,40)
    mach=make_machine(rng,ns,nw,m); Hin=[rng.randrange(nw) for _ in range(m)]; C0=rng.randrange(ns)
    Cstar,reads=run(mach,Hin,C0,N); a=rank(reads,N); AN=max(a)
    Z=[C0]+[rng.randrange(ns) for _ in range(N)]
    r=0; hist=[Z]
    while True:
        Znew=H(mach,Hin,Z,N)
        for t in range(N+1):
            if a[t]<=r: assert Znew[t]==Cstar[t], ("claim fails",trial,t,r)
        r+=1
        if Znew==Z: break
        Z=Znew
        assert r<=AN+2
    assert Z==Cstar   # fixpoint is the real execution
    # rounds until exact (first r with Z^(r)=C*) <= AN+1
    trials+=1
print("random machines ok:",trials)
# fixed-lag copy: v_t = v_{t-d}; history: d initial words (ones); stage t reads word written at stage t-d
for d in [1,2,3,5]:
    for N in [10,37,100]:
        m=d
        # state = (current word) ; p depends on stage: address of word v_{t-d}
        # model: stage t appends v_{t-1}? we implement directly: C_t = v_t, appended word at stage s is C_{s-1}... use explicit simulation
        # stage t reads cell holding v_{t-d}: initial cell for t<=d, else cell written at stage s with appended word C_{s-1}=v_{s-1} -> s=t-d+1
        reads=[None]
        for t in range(1,N+1):
            if t<=d: reads.append(('init',))
            else: reads.append(('int',t-d+1))
        a=rank(reads,N)
        print("lag",d,"N",N,"A_N",max(a))
