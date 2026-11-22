# Sanity check of the LR-SPAI summaries: leaf transcript summaries, pullback merge,
# syndrome recompression, compared with direct simulation on all inputs.
import random, itertools
def rref(rows, d):
    rows=[r for r in rows]; basis=[]; piv=[]
    for r in rows:
        for b,p in zip(basis,piv):
            if r>>p &1: r^=b
        if r:
            p=r.bit_length()-1
            # reduce existing
            nb=[]
            for b in basis:
                if b>>p&1: b^=r
                nb.append(b)
            basis=nb+[r]; piv=piv+[p]
    return basis,piv
def dot(r,x): return bin(r&x).count('1')&1
def matvec(M,x,d):  # M list of d row-masks
    y=0
    for i in range(d):
        if dot(M[i],x): y|=1<<i
    return y
def matmul(A,B,d): # (A B) rows: row i of AB = sum_j A[i][j] B[j]
    C=[]
    for i in range(d):
        r=0
        for j in range(d):
            if A[i]>>j&1: r^=B[j]
        C.append(r)
    return C
def rowtimes(r,M,d): # row vector r times matrix M
    out=0
    for j in range(d):
        if r>>j&1: out^=M[j]
    return out
def rand_inst(m,d,T,sens_prob):
    st=[]
    for t in range(T):
        sens = random.random()<sens_prob
        a=[random.randrange(d) for u in range(m)]
        if sens: g=[[random.randrange(m) for z in range(2)] for u in range(m)]
        else:
            g=[]
            for u in range(m):
                q=random.randrange(m); g.append([q,q])
        A=[[random.getrandbits(d) if random.random()<0.5 else (1<<i) for i in range(d)] for u in range(m)]
        b=[random.getrandbits(d) for u in range(m)]
        st.append(dict(sens=sens,a=a,g=g,A=A,b=b))
    return st
def simulate(st,lo,hi,u,x,d):
    for t in range(lo,hi):
        s=st[t]; z=x>>s['a'][u]&1
        nx=matvec(s['A'][u],x,d)^s['b'][u]; u=s['g'][u][z]; x=nx
    return u,x
def leaf_summary(st,lo,hi,m,d):
    sensidx=[t for t in range(lo,hi) if st[t]['sens']]
    S={}
    I=[1<<i for i in range(d)]
    for u in range(m):
        leaves=[]
        for tau in itertools.product([0,1],repeat=len(sensidx)):
            M=I[:]; c=0; q=u; rows=[]; rhs=[]; k=0
            for t in range(lo,hi):
                s=st[t]; a=s['a'][q]
                row=M[a]; rows.append(row); r=(c>>a&1)
                if s['sens']:
                    z=tau[k]; k+=1; rows_r=(row, z^r)
                    leaves_eq=rows_r
                    rhs.append(leaves_eq)
                else: z=0
                A=s['A'][q]; M=matmul(A,M,d); c=matvec(A,c,d)^s['b'][q]; q=s['g'][q][z]
            # consistency of rhs system
            sysrows=[(r,v) for r,v in rhs]
            if consistent(sysrows,d):
                leaves.append(dict(G=sysrows,q=q,M=M,c=c))
        S[u]=leaves
    return S
def consistent(sysrows,d):
    basis=[]  # (row,val) reduced
    for r,v in sysrows:
        for br,bv in basis:
            p=br.bit_length()-1
            if r>>p&1: r^=br; v^=bv
        if r==0:
            if v: return False
            continue
        basis.append((r,v))
    return True
def holds(G,x): return all(dot(r,x)==v for r,v in G)
def merge(S1,S2,m,d):
    S={}; maxrank=0
    for u in range(m):
        pairs=[]
        for lam in S1[u]:
            for mu in S2[lam['q']]:
                G=lam['G']+[(rowtimes(r,lam['M'],d), v^dot(r,lam['c'])) for r,v in mu['G']]
                if consistent(G,d): pairs.append((lam,mu,G))
        rows=[r for (_,_,G) in pairs for r,_ in G]
        basis,piv=rref(rows,d); rho=len(basis); maxrank=max(maxrank,rho)
        leaves=[]
        for s in itertools.product([0,1],repeat=rho):
            # representative: x with basis_i . x = s_i ; reduced basis has distinct pivots and pivot columns cleared in others
            x=0
            for bi,p,si in zip(basis,piv,s):
                if si: x|=1<<p
            assert all(dot(bi,x)==si for bi,si in zip(basis,s))
            act=[pr for pr in pairs if holds(pr[2],x)]
            assert len(act)==1
            lam,mu,G=act[0]
            leaves.append(dict(G=[(bi,si) for bi,si in zip(basis,s)],q=mu['q'],M=matmul(mu['M'],lam['M'],d),c=matvec(mu['M'],lam['c'],d)^mu['c']))
        S[u]=leaves
    return S,maxrank
def build(st,blocks,m,d):
    if len(blocks)==1: return leaf_summary(st,blocks[0][0],blocks[0][1],m,d),0
    h=len(blocks)//2
    L,r1=build(st,blocks[:h],m,d); R,r2=build(st,blocks[h:],m,d)
    S,r=merge(L,R,m,d); return S,max(r,r1,r2)
random.seed(1); bad=0; trials=0; ranks=[]
for trial in range(150):
    m=random.randint(1,3); d=random.randint(1,5); T=random.randint(1,14); h0=random.randint(1,3)
    st=rand_inst(m,d,T,0.5)
    # canonical blocks: cut after every h0 sensitive stages
    blocks=[]; lo=0; cnt=0
    for t in range(T):
        if st[t]['sens']:
            cnt+=1
            if cnt==h0 and t<T-1: blocks.append((lo,t+1)); lo=t+1; cnt=0
    blocks.append((lo,T))
    S,mr=build(st,blocks,m,d); ranks.append(mr)
    for u in range(m):
        for x in range(1<<d):
            act=[l for l in S[u] if holds(l['G'],x)]
            trials+=1
            if len(act)!=1: bad+=1; continue
            l=act[0]; uu,xx=simulate(st,0,T,u,x,d)
            if (l['q'],matvec(l['M'],x,d)^l['c'])!=(uu,xx): bad+=1
print("checked",trials,"(u,x) pairs; violations",bad,"; max merge rank seen",max(ranks))
