"""EXACT check (integer polynomial arithmetic) that explicit 5x5 spaces are level: perm(J + sum x_k B_k) == 120 identically."""
import itertools, sys
from fractions import Fraction
def pmul(p,q):
    r={}
    for a,ca in p.items():
        for b,cb in q.items():
            k=tuple(x+y for x,y in zip(a,b)); r[k]=r.get(k,0)+ca*cb
    return {k:v for k,v in r.items() if v!=0}
def padd(p,q):
    r=dict(p)
    for k,v in q.items(): r[k]=r.get(k,0)+v
    return {k:v for k,v in r.items() if v!=0}
def level_identity(B):
    d=len(B); zero=tuple([0]*d)
    def lin(i,j):
        p={zero:1}
        for k in range(d):
            if B[k][i][j]!=0:
                e=[0]*d; e[k]=1; p[tuple(e)]=B[k][i][j]
        return p
    L=[[lin(i,j) for j in range(5)] for i in range(5)]
    # permanent by expansion along rows with memo on column subsets (Ryser-free DP)
    from functools import lru_cache
    memo={}
    def rec(i,cols):
        if i==5: return {zero:1}
        key=(i,cols)
        if key in memo: return memo[key]
        tot={}
        for j in cols:
            tot=padd(tot,pmul(L[i][j],rec(i+1,tuple(c for c in cols if c!=j))))
        memo[key]=tot; return tot
    P=rec(0,(0,1,2,3,4))
    const=P.get(zero,0); rest={k:v for k,v in P.items() if k!=zero}
    return const,rest
def rank(rows):
    M=[[Fraction(x) for x in r] for r in rows]; r=0
    for c in range(len(M[0])):
        p=None
        for i in range(r,len(M)):
            if M[i][c]!=0: p=i; break
        if p is None: continue
        M[r],M[p]=M[p],M[r]
        for i in range(len(M)):
            if i!=r and M[i][c]!=0:
                f=M[i][c]/M[r][c]; M[i]=[a-f*b for a,b in zip(M[i],M[r])]
        r+=1
        if r==len(M): break
    return r
def E(i,j,v=1):
    M=[[0]*5 for _ in range(5)]; M[i][j]=v; return M
def madd(*Ms):
    return [[sum(M[i][j] for M in Ms) for j in range(5)] for i in range(5)]
def rowmat(i,w): return [[w[j] if a==i else 0 for j in range(5)] for a in range(5)]
def colmat(j,u): return [[u[a] if b==j else 0 for b in range(5)] for a in range(5)]
def Lm(m,c=0,Wbasis=None):
    """rows 0..4; split free row on rows (2,4): e_2 m^T, e_4 w^T (w in {1,m}^perp); column 2: x e_2^T (x sum-zero on rows 0,1,3);
       column 4: (1,1,-3,1,0); optional shear c."""
    assert sum(m)==0 and m[4]==0
    B=[rowmat(2,m)]
    for w in Wbasis:
        assert sum(w)==0 and sum(a*b for a,b in zip(w,m))==0
        B.append(rowmat(4,w))
    B.append(madd(colmat(2,[1,0,0,-1,0]),colmat(4,[0,c,-c,0,0])))
    B.append(madd(colmat(2,[0,1,0,-1,0]),colmat(4,[0,c,-2*c,c,0])))
    B.append(colmat(4,[1,1,-3,1,0]))
    return B
def free_dims(B):
    d=len(B); flat=lambda M,keep:[M[i][j] for i in range(5) for j in range(5) if keep(i,j)]
    fr=[d-rank([flat(M,lambda i,j,r=r:i!=r) for M in B]) for r in range(5)]
    fc=[d-rank([flat(M,lambda i,j,c=c:j!=c) for M in B]) for c in range(5)]
    return fr,fc
if __name__=='__main__':
    m=[1,2,-4,1,0]
    # W = {w: sum w = 0, w.m = 0}: basis
    Wb=[[0,0,0,1,-1],[1,0,0,-1,0],[2,1,1,0,-4]]   # checks: sums 0; w.m: 1*... verify by assert
    Wb=[[1,0,0,-1,0],[4,0,1,0,-5],[2,-1,0,0,-1]]
    for c in (0,1):
        B=Lm(m,c,Wb); d=rank([[M[i][j] for i in range(5) for j in range(5)] for M in B])
        const,rest=level_identity(B)
        print('m =',m,'c =',c,': dim',d,' perm(J+t) constant term',const,' number of nonzero non-constant coefficients',len(rest),' free row dims, free col dims',free_dims(B))
