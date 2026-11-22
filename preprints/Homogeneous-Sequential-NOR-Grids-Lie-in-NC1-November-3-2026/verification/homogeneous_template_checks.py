import itertools, sys
# 1-indexed grid: X[i][j], i=0 top boundary, j=0 west boundary
def evalgrid(T, L, alpha, beta):
    H=len(L); W=len(T)
    X=[[0]*(W+1) for _ in range(H+1)]
    for j in range(1,W+1): X[0][j]=T[j-1]
    for i in range(1,H+1):
        X[i][0]=L[i-1]
        for j in range(1,W+1):
            X[i][j]=(X[i][j-1]^alpha[i-1]) & (X[i-1][j]^beta[i-1][j-1])
    return X

def bits(n,k): return [ (n>>t)&1 for t in range(k)]

def check_v169(Hmax=5,Wmax=6):
    bad=0; cnt=0
    for H in range(1,Hmax+1):
      AH={0,1,2,H}
      for W in range(1,Wmax+1):
        for bb in range(1<<W):
          b=bits(bb,W)
          for tt in range(1<<W):
            T=bits(tt,W)
            for ll in range(1<<H):
              L=bits(ll,H)
              X=evalgrid(T,L,[1]*H,[b]*H); cnt+=1
              # threshold columns
              for j in range(1,W+1):
                if b[j-1]==0:
                  run=T[j-1]
                  for i in range(1,H+1):
                    run=run & (1-X[i][j-1])
                    if X[i][j]!=run: bad+=1
              # dense slabs: maximal runs of b=1
              j=1
              while j<=W:
                if b[j-1]==1:
                  c=j
                  while j<=W and b[j-1]==1: j+=1
                  d=j-1
                  for i in range(3,H+1):
                    for jj in range(c+2,d+1):
                      if X[i][jj]!=X[i-1][jj-1]: bad+=1
                  # no vertical 000 in dense columns after first
                  for jj in range(c+1,d+1):
                    for i in range(3,H+1):
                      if X[i][jj]==0 and X[i-1][jj]==0 and X[i-2][jj]==0: bad+=1
                else: j+=1
    print("v169 lemmas: instances",cnt,"violations",bad)

def thr_state(col):  # col list of H bits; return s if threshold 1^s0^(H-s) else None
    H=len(col); s=0
    while s<H and col[s]==1: s+=1
    if any(col[s:]): return None
    return s

def check_transfers(Hmax=6,Wmax=7):
    bad=0; types=set()
    for H in range(3,Hmax+1):
      AH={0,1,2,H}
      for W in range(2,Wmax+1):
        # block: column 1 is a zero column (source), columns 2..W: 1^r 0 with r=W-2
        r=W-2
        b=[0]+[1]*r+[0]
        for tt in range(1<<W):
          T=bits(tt,W)
          F=[]
          for s in range(H+1):
            # set west so that column 1 = theta_s: use T[0]=1 and L appropriately: simpler -> directly build
            X=[[0]*(W+1) for _ in range(H+1)]
            for j in range(1,W+1): X[0][j]=T[j-1]
            for i in range(1,H+1):
              X[i][1]=1 if i<=s else 0
              for j in range(2,W+1):
                X[i][j]=(1-X[i][j-1]) & (X[i-1][j]^b[j-1])
            st=thr_state([X[i][W] for i in range(1,H+1)])
            if st is None: bad+=1
            F.append(st)
          if F[0] not in AH or F[1] not in AH: bad+=1
          tail=F[2:]
          if not (all(x==tail[0] for x in tail) and tail[0] in AH) and tail!=list(range(2,H+1)): bad+=1
          types.add((H,tuple(F)))
    print("transfer classification violations",bad)
    # closure of G_H
    for H in range(3,9):
        AH=[0,1,2,H]; G=[]
        for f0 in AH:
          for f1 in AH:
            for tau in AH+['id']:
              f=[f0,f1]+([tau]*(H-1) if tau!='id' else list(range(2,H+1)))
              G.append(tuple(f))
        Gs=set(G)
        ok=all(tuple(f[g[s]] for s in range(H+1)) in Gs for f in G for g in G)
        print("H",H,"|G_H|",len(Gs),"closed",ok)

check_v169()
check_transfers()
