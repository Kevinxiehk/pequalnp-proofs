# verify2 r8: EXACT (T2) test (stage2 R6-7) for the survivor (S3) of R9-4, over Q (Fractions), all cubic coefficients (no sampling).
# X (rows 1..4 of the 5x5, row r = 0 zero): C kappa' e_0^T + e_3 (x) span{(-4,1,1,1,1),(0,1,-1,0,0)} + e_4 (x) span{(0,0,0,1,-1),(0,1,1,-1,-1)},
# kappa' = (sg,-1-sg,0,1).  (T2): exists T_0..T_4 (4x5) with D_{T_k} G_j + D_{T_j} G_k == 0 on X (j <= k) and sum_k T_k = J' mod X.
import sys, itertools
from fractions import Fraction as F
def basis(sg):
    B=[]
    M=[[0]*5 for _ in range(4)]; col=[sg,-1-sg,0,1]
    for i in range(4): M[i][0]=F(col[i])
    B.append(M)
    for row,w in ((2,(-4,1,1,1,1)),(2,(0,1,-1,0,0)),(3,(0,0,0,1,-1)),(3,(0,1,1,-1,-1))):
        M=[[F(0)]*5 for _ in range(4)]; M[row]=[F(x) for x in w]; B.append(M)
    return B
NV=5
def padd(a,b,c=1):
    r=dict(a)
    for k,v in b.items():
        x=r.get(k,0)+c*v
        if x: r[k]=x
        elif k in r: del r[k]
    return r
def pmul(a,b):
    r={}
    for k1,v1 in a.items():
        for k2,v2 in b.items():
            k=tuple(x+y for x,y in zip(k1,k2)); r[k]=r.get(k,0)+v1*v2
    return {k:v for k,v in r.items() if v}
def entry(B,i,l):   # polynomial in c of xi[i][l]
    out={}
    for q in range(NV):
        if B[q][i][l]:
            e=[0]*NV; e[q]=1; out[tuple(e)]=out.get(tuple(e),0)+B[q][i][l]
    return out
def perm(Mp):
    n=len(Mp); tot={}
    for s in itertools.permutations(range(n)):
        t={tuple([0]*NV):F(1)}
        for i in range(n):
            t=pmul(t,Mp[i][s[i]])
            if not t: break
        tot=padd(tot,t)
    return tot
def rank_frac(rows,ncol):
    M=[r[:] for r in rows]; rk=0
    for c in range(ncol):
        piv=next((i for i in range(rk,len(M)) if M[i][c]!=0),None)
        if piv is None: continue
        M[rk],M[piv]=M[piv],M[rk]; pv=M[rk][c]
        M[rk]=[x/pv for x in M[rk]]
        for i in range(len(M)):
            if i!=rk and M[i][c]!=0:
                f=M[i][c]; M[i]=[x-f*y for x,y in zip(M[i],M[rk])]
        rk+=1
    return rk
import numpy as np
def S1():
    A=np.load('/home/kevxhk/work/L-gct-210/stage2/r9/cand_D04_MAi_f2.npy').real
    return [[[F(int(round(A[q,i,l]))) for l in range(5)] for i in range(4)] for q in range(5)]
def S2(sg):
    B=[]
    M=[[F(0)]*5 for _ in range(4)]; col=[sg,-1-sg,0,1]
    for i in range(4): M[i][0]=F(col[i])
    B.append(M)
    for row,w in ((2,(-4,1,1,1,1)),(2,(0,1,-1,0,0)),(2,(0,-1,-1,1,1)),(3,(0,0,0,1,-1))):
        M=[[F(0)]*5 for _ in range(4)]; M[row]=[F(x) for x in w]; B.append(M)
    return B
cases=[('S1',S1())]+[('S2 sg=%s'%s,S2(s)) for s in (F(0),F(1),F(2),F(1,3))]
for name,Bq in cases:
    sg=name
    basis=lambda _s, Bq=Bq: Bq
    B=basis(sg); X=[[entry(B,i,l) for l in range(5)] for i in range(4)]
    # order 1: G_j(xi) = perm of X without column j  must vanish identically
    G=[perm([[X[i][l] for l in range(5) if l!=j] for i in range(4)]) for j in range(5)]
    g_ok=all(not g for g in G)
    # level of the 5x5 (row 0 zero): perm(J + x) - 120, exact polynomial
    one={tuple([0]*NV):F(1)}
    J5=[[one]*5]+[[padd(one,X[i][l]) for l in range(5)] for i in range(4)]
    lev=padd(perm(J5),{tuple([0]*NV):F(120)},-1)
    # D_j[i][l] = perm3(X without row i, columns j,l)
    D=[[[{} if l==j else perm([[X[a][c] for c in range(5) if c not in (j,l)] for a in range(4) if a!=i]) for l in range(5)] for i in range(4)] for j in range(5)]
    # unknowns: T[k][i][l] -> index k*20+i*5+l (100), then d_q (5)
    rows=[]
    for j in range(5):
        for k in range(j,5):
            poly={}   # monomial -> dict unknown -> coeff
            for (kk,jj) in ((k,j),(j,k)):
                for i in range(4):
                    for l in range(5):
                        for mon,cf in D[jj][i][l].items():
                            poly.setdefault(mon,{}); u=kk*20+i*5+l; poly[mon][u]=poly[mon].get(u,0)+cf
            for mon,coeffs in poly.items():
                r=[F(0)]*106
                for u,cf in coeffs.items(): r[u]+=cf
                if any(r): rows.append(r)
    nT2=len(rows)
    # sum_k T_k + sum_q d_q B_q = J'  (augmented column 105)
    aug=[]
    for i in range(4):
        for l in range(5):
            r=[F(0)]*106
            for k in range(5): r[k*20+i*5+l]=F(1)
            for q in range(5): r[100+q]=B[q][i][l]
            r[105]=F(1); aug.append(r)
    allrows=rows+aug
    rc=rank_frac([r[:105] for r in allrows],105); ra=rank_frac(allrows,106)
    rT=rank_frac([r[:100] for r in rows],100)
    print('sg=%s: G==0 on X: %s; level poly zero: %s; (T2) eqs %d, rank on T %d (solution space dim %d); consistency: rank coef %d, rank aug %d -> %s'
          %(sg,g_ok,not lev,nT2,rT,100-rT,rc,ra,'SOLVABLE' if ra==rc else 'NOT SOLVABLE (T2 kills X)'),flush=True)
