# (1) EXACT FO2 certificate for M*: exact basis of ker(A) (contains T_1(M*); dim 11), exact Hessian form q_Y = D^2 perm(J + (Y;0)) at integer
#     points Y of M*, restricted to that kernel; rank_Q >= 5  =>  every level space containing M* has dim <= 11 - ceil(5/2) = 8.
#     (Isotropy holds on L inside T_1 inside ker A, so using ker A is legitimate; the bound is dim ker A - ceil(rank/2).)
# (2) numerical invariants of other members of the family (x, y) and FO2.
import sys, itertools, random; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
from fractions import Fraction as Fr
from exact_T1 import nullspace, cof
from mstar2 import B
P3=list(itertools.permutations(range(3)))
def perm3(A): return sum(A[0][p[0]]*A[1][p[1]]*A[2][p[2]] for p in P3)
def hess(M):
    H=[[Fr(0)]*25 for _ in range(25)]
    for i in range(5):
        for k in range(i+1,5):
            rows=[r for r in range(5) if r not in (i,k)]
            for j in range(5):
                for l in range(5):
                    if j==l: continue
                    cols=[c for c in range(5) if c not in (j,l)]
                    v=perm3([[M[r][c] for c in cols] for r in rows]); H[5*i+j][5*k+l]=v; H[5*k+l][5*i+j]=v
    return H
def rankQ(A):
    A=[row[:] for row in A]; r=0
    for c in range(len(A[0])):
        p=next((i for i in range(r,len(A)) if A[i][c]!=0),None)
        if p is None: continue
        A[r],A[p]=A[p],A[r]
        for i in range(r+1,len(A)):
            if A[i][c]!=0:
                f=A[i][c]/A[r][c]; A[i]=[a-f*b for a,b in zip(A[i],A[r])]
        r+=1
        if r==len(A): break
    return r
random.seed(3); d=len(B); rows=[]
pt=lambda c:[[Fr(1)+sum(c[k]*B[k][i][j] for k in range(d)) if i<4 else Fr(1) for j in range(5)] for i in range(5)]
for _ in range(320): rows.append(cof(pt([random.randint(-4,4) for _ in range(d)])))
R,N=nullspace(rows,25); n=len(N); print('dim ker A =',n)
best=0
for trial in range(4):
    H=hess(pt([random.randint(-3,3) for _ in range(d)]))
    Q=[[sum(N[a][p]*sum(H[p][q]*N[b][q] for q in range(25)) for p in range(25)) for b in range(n)] for a in range(n)]
    r=rankQ(Q); best=max(best,r); print('  exact rank of q_Y on ker A at an integer point Y:',r)
print('EXACT: every level space containing M* has dim <= %d - ceil(%d/2) = %d'%(n,best,n-(best+1)//2))
import numpy as np
from t import *
from a1 import embed, defect
from a5 import onb
from a6 import T1
from r5_FO2 import FO2
w=np.exp(2j*np.pi/3)
def fam(x,y):
    Bn=[]
    for c in (0,3,4):
        m=np.zeros((4,5),complex); m[3,c]=2; m[3,1]=-1; m[3,2]=-1; Bn.append(m)
    m=np.zeros((4,5),complex); m[:3,0]=x; Bn.append(m)
    m=np.zeros((4,5),complex); m[:3,3]=y; Bn.append(m)
    m=np.zeros((4,5),complex); m[2,1]=1; m[2,2]=-1; Bn.append(m)
    return np.array(Bn)
rg=np.random.default_rng(0)
for name,x,y in (('x=(2,-1,-1), y=(0,1,-1)',[2,-1,-1],[0,1,-1]),('x=y=(1,w,w^2) isotropic',[1,w,w*w],[1,w,w*w]),('x=(1,2,-3), y=(5,-4,-1)',[1,2,-3],[5,-4,-1])):
    Bo=onb(fam(x,y)); T=T1(embed(Bo),rg,npts=120); S=np.linalg.svd(T[:,4,:],compute_uv=False)
    print('%-28s level err %.1e dim T1 %d dim Omega %d FO2 %s'%(name,level_err(Bo,ntest=60),len(T),int((S>1e-8).sum()),FO2(embed(Bo),rg)))
