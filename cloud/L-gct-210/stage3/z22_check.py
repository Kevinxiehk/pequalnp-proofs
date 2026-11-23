# Round 7, section 26 (B''): sanity checks for Theorem Z22 (two rows with 2-dim single-row parts are impossible).
import numpy as np, itertools
rg=np.random.default_rng(3)
def rank(A,tol=1e-9):
    s=np.linalg.svd(np.atleast_2d(A),compute_uv=False); return int((s>tol*max(1,s[0])).sum())
def null(A,tol=1e-9):
    u,s,vh=np.linalg.svd(A); r=int((s>tol*max(1,s[0])).sum()); return vh[r:].conj().T
one=np.ones(5)
# orthonormal basis f_1..f_4 of 1^perp (real), isotropic vectors f_1 + i f_2 etc.
Q,_=np.linalg.qr(np.column_stack([one,rg.normal(size=(5,4))])); F=Q[:,1:]
cnt={}
for trial in range(200):
    O,_=np.linalg.qr(rg.normal(size=(4,4))); G=F@O                      # random real orthonormal frame of 1^perp
    n=G[:,0]+1j*G[:,1]; h=G[:,2]+1j*G[:,3]                              # totally isotropic plane Z = span(n,h) in 1^perp
    assert abs(n@n)<1e-12 and abs(h@h)<1e-12 and abs(n@h)<1e-12 and abs(n.sum())<1e-12
    d=rank(np.array([n*n,n*h,h*h])); cnt[('deg-2: dim Z o Z',d)]=cnt.get(('deg-2: dim Z o Z',d),0)+1
    # (deg-1): U = span(n, g), U' = span(n, g') with g = G[:,2], g' = G[:,3] (non-isotropic, orthogonal): radical = C n
    g=G[:,2]; gp=G[:,3]; d1=rank(np.array([n*n,n*g,n*gp,g*gp])); cnt[('deg-1: dim U o U\'',d1)]=cnt.get(('deg-1: dim U o U\'',d1),0)+1
    # Lemma DEG: symmetric zero-diagonal B with B V_3 = 0, V_3 = span(n,g,gp): B = x 11^T + y(1 n^T + n 1^T) + z n n^T with zero diagonal
    A=np.array([[1,2*n[j],n[j]**2] for j in range(5)]); k=3-rank(A); cnt[('Lemma DEG: dim of such B',k)]=cnt.get(('Lemma DEG: dim of such B',k),0)+1
for k,v in sorted(cnt.items()): print(k,v)
# --- exact check of the degree-1 identities of STEP 1 (random rational data, Fractions, interpolation in t)
from fractions import Fraction as Fr
from itertools import permutations
import random
random.seed(5)
def rv(): return [Fr(random.randint(-6,6),random.randint(1,3)) for _ in range(5)]
def perm(M): 
    tot=Fr(0)
    for q in permutations(range(5)):
        v=Fr(1)
        for i in range(5): v*=M[i][q[i]]
        tot+=v
    return tot
def P(t,la,lb,Y,a,b,u,up):
    M=[[1+t*Y[i][j] for j in range(5)] for i in range(3)]+[[1+t*a[j]+la*u[j] for j in range(5)],[1+t*b[j]+lb*up[j] for j in range(5)]]
    return perm(M)
def lincoef(vals):      # vals[k] = f(k), k = 0..5, deg f <= 5: coefficient of t^1 by solving the Vandermonde system exactly
    n=6; A=[[Fr(k)**e for e in range(n)]+[vals[k]] for k in range(n)]
    for c in range(n):
        piv=next(r for r in range(c,n) if A[r][c]!=0); A[c],A[piv]=A[piv],A[c]
        A[c]=[x/A[c][c] for x in A[c]]
        for r in range(n):
            if r!=c and A[r][c]!=0: A[r]=[x-A[r][c]*y for x,y in zip(A[r],A[c])]
    return A[1][n]
ok=True
for trial in range(3):
    Y=[rv() for _ in range(3)]; a=rv(); b=rv(); u=rv(); u[4]=-sum(u[:4])
    while True:
        up=rv(); det=u[4]-u[3]
        if det!=0: break
    # solve x + y = -sum(up[:3]),  u3 x + u4 y = -sum(u_i up_i, i<3)
    r1=-sum(up[:3]); r2=-sum(u[i]*up[i] for i in range(3)); x=(r1*u[4]-r2)/(u[4]-u[3]); y=r1-x; up[3]=x; up[4]=y
    assert sum(up)==0 and sum(u[i]*up[i] for i in range(5))==0 and sum(u)==0
    c=[sum(Y[r][j] for r in range(3)) for j in range(5)]
    c11=lincoef([P(Fr(k),1,1,Y,a,b,u,up)-P(Fr(k),1,0,Y,a,b,u,up)-P(Fr(k),0,1,Y,a,b,u,up)+P(Fr(k),0,0,Y,a,b,u,up) for k in range(6)])
    c10=lincoef([P(Fr(k),1,0,Y,a,b,u,up)-P(Fr(k),0,0,Y,a,b,u,up) for k in range(6)])
    c01=lincoef([P(Fr(k),0,1,Y,a,b,u,up)-P(Fr(k),0,0,Y,a,b,u,up) for k in range(6)])
    e11=4*sum(c[j]*u[j]*up[j] for j in range(5)); e10=-6*sum(u[j]*(b[j]+c[j]) for j in range(5)); e01=-6*sum(up[j]*(a[j]+c[j]) for j in range(5))
    ok=ok and c11==e11 and c10==e10 and c01==e01
print("STEP 1 degree-1 identities (t la lb: 4<c,u o u'>;  t la: -6<u,b+c>;  t lb: -6<u',a+c>) exact on 3 random rational instances:",ok)
