import itertools, random
from collections import Counter
# permutations of {0..4} as tuples; product right-to-left: (p*q)(i) = p(q(i))
def mul(p,q): return tuple(p[q[i]] for i in range(5))
def inv(p):
    r=[0]*5
    for i,x in enumerate(p): r[x]=i
    return tuple(r)
E=tuple(range(5))
def parity(p):
    s=0
    for i in range(5):
        for j in range(i+1,5):
            if p[i]>p[j]: s+=1
    return s%2
A5=[p for p in itertools.permutations(range(5)) if parity(p)==0]
assert len(A5)==60
def cyc(*c):
    p=list(range(5))
    c=[x-1 for x in c]
    for i in range(len(c)): p[c[i]]=c[(i+1)%len(c)]
    return tuple(p)
def order(p):
    k=1;q=p
    while q!=E: q=mul(q,p);k+=1
    return k
def pw(p,k):
    r=E
    for _ in range(k): r=mul(r,p)
    return r
# ---- #30 Thm 11
Dp=Counter(); Dm=Counter(); bad=[]
for A in A5:
    for B in A5:
        dp=sum(1 for r in A5 if r==mul(mul(A,r),B))
        dm=sum(1 for r in A5 if r==mul(mul(A,inv(r)),B))
        Dp[dp]+=1; Dm[dm]+=1
        if dp==60 and not (A==E and B==E): bad.append(('p60',A,B))
        if (dm==16)!=(A==B): bad.append(('m16',A,B))
        if dm==0 and order(mul(inv(A),B))!=2: bad.append(('m0',A,B))
print('Thm11 eps=+1 size distribution', sorted(Dp.items()))
print('Thm11 eps=-1 size distribution', sorted(Dm.items()))
print('Thm11 violations', bad[:3], len(bad))
# ---- #29 Lemma 2, Thm 3
a=cyc(1,2,3,4,5); b=cyc(1,2,4,5,3); c=cyc(3,5,4); d=cyc(2,4,3)
comm=lambda x,z: mul(mul(mul(inv(x),inv(z)),x),z)
print('c^-1 a c == b:', mul(mul(inv(c),a),c)==b)
print('[a,b] == (1 4 2 3 5):', comm(a,b)==cyc(1,4,2,3,5))
print('d^-1 [a,b] d == a:', mul(mul(inv(d),comm(a,b)),d)==a)
print('all even:', all(parity(p)==0 for p in [a,b,c,d]))
enc={0:E,1:a}
NOT=lambda x: mul(a,pw(x,4))
AND=lambda x,y: mul(mul(inv(d), comm(x, mul(mul(inv(c),y),c))), d)
ok=all(NOT(enc[u])==enc[1-u] for u in (0,1)) and all(AND(enc[u],enc[v])==enc[u&v] for u in (0,1) for v in (0,1))
print('NOT/AND gadgets correct:', ok)
# gadget written with fourth powers instead of inverses
AND4=lambda x,y: mul(mul(mul(mul(mul(mul(inv(d),pw(x,4)), mul(mul(inv(c),pw(y,4)),c)), x), mul(mul(inv(c),y),c)), E), d)
print('AND gadget with 4th powers correct:', all(AND4(enc[u],enc[v])==enc[u&v] for u in (0,1) for v in (0,1)))
# ---- #27 Lemma 2 composition & Thm 3 bijection, random cycles
def desc_apply(D,x):
    A,B,e=D; return mul(mul(A, x if e==1 else inv(x)),B)
def compose(g,f):  # g after f
    A,B,e=f; C,D,d=g
    if d==1: return (mul(C,A), mul(B,D), e)
    return (mul(C,inv(B)), mul(inv(A),D), -e)
for _ in range(200):
    f=(random.choice(A5),random.choice(A5),random.choice([1,-1]))
    g=(random.choice(A5),random.choice(A5),random.choice([1,-1]))
    x=random.choice(A5)
    assert desc_apply(g,desc_apply(f,x))==desc_apply(compose(g,f),x)
print('descriptor composition formula ok')
# local factor z=xy with two cycle vars (in,out) and third p; return descriptor out=A in^e B and a checker
def local(role_in, role_out, p):
    # roles among 'x','y','z'
    if (role_in,role_out)==('x','y'): return (E,p,-1)            # y = x^-1 p (p=z)
    if (role_in,role_out)==('y','x'): return (p,E,-1)            # x = p y^-1 (p=z)
    if (role_in,role_out)==('x','z'): return (E,p,1)             # z = x p (p=y)
    if (role_in,role_out)==('z','x'): return (E,inv(p),1)        # x = z p^-1 (p=y)
    if (role_in,role_out)==('y','z'): return (p,E,1)             # z = p y (p=x)
    if (role_in,role_out)==('z','y'): return (inv(p),E,1)        # y = p^-1 z (p=x)
def holds(role_in,role_out,p,vin,vout):
    val={role_in:vin, role_out:vout}
    third=({'x','y','z'}-{role_in,role_out}).pop(); val[third]=p
    return val['z']==mul(val['x'],val['y'])
pairs=[('x','y'),('y','x'),('x','z'),('z','x'),('y','z'),('z','y')]
for trial in range(60):
    m=random.choice([2,3])
    fac=[(random.choice(pairs),random.choice(A5)) for _ in range(m)]
    # factor i links q_i -> q_{i+1}
    brute=0
    for qs in itertools.product(A5,repeat=m):
        if all(holds(fac[i][0][0],fac[i][0][1],fac[i][1],qs[i],qs[(i+1)%m]) for i in range(m)): brute+=1
    D=(E,E,1)
    for i in range(m):
        D=compose(local(fac[i][0][0],fac[i][0][1],fac[i][1]),D)
    roots=sum(1 for r in A5 if desc_apply(D,r)==r)
    assert brute==roots,(brute,roots)
print('symbolic cycle opening: brute-force assignment count == root count on 60 random cycles')
# ---- #27 Lemma 10 mixer
okm=True
for x in A5:
    for v in A5:
        sols=[(y,mul(x,y)) for y in A5 if mul(mul(x,y),y)==v]
        roots=[y for y in A5 if mul(y,y)==mul(inv(x),v)]
        if sorted(s[0] for s in sols)!=sorted(roots): okm=False
print('mixer opening y^2 = x^-1 v equivalent:', okm)
# mixer bijectivity and inverse
print('mixer bijective:', len({(mul(x,y),mul(mul(x,y),y)) for x in A5 for y in A5})==3600)
print('mixer inverse formula:', all((lambda u,v: (mul(mul(u,inv(v)),u), mul(inv(u),v)))(mul(x,y),mul(mul(x,y),y))==(x,y) for x in A5 for y in A5))
# square roots in A5
sq=Counter(mul(x,x) for x in A5)
print('square-root counts by class order:', sorted(Counter((order(g),sq[g]) for g in A5).items()))
cent=Counter(order(g) for g in A5)
print('class orders count', cent)
