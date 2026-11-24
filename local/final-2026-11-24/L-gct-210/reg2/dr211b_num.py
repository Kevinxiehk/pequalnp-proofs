# numerical invariants of the pattern (2,1,1|2), incidence case (ii):
#   M = e_0 (x) span(5e_0-1, (0,a)) (+) C e_1 (0,b)^T (+) C e_2 (0,c)^T (+) {x e_0^T : x_0 = 0, sum x = 0}
#   a, b, c in H = sum-zero vectors of C^4 (columns 1..4), pairwise orthogonal (bilinear), T(a,b,c) = sum_j a_j b_j c_j = 0.
#   (hand: P_1 = 0, P_2 = -(y2y3<a,b> + y2y4<a,c> + y3y4<b,c>), P_3 = 2 y2y3y4 T, P_4 = 2 x3 y2y3y4 T.)
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from t import *
from a1 import embed, defect, phirank
from a5 import onb
from a6 import T1, E0
from r5_FO2 import FO2
np.set_printoptions(precision=3,suppress=True,linewidth=200)
def cross4(b,c):
    # a_j = signed 3x3 minors of [1;b;c] : a is orthogonal to 1, b, c (bilinear)
    A=np.array([np.ones(4),b,c],complex); a=np.zeros(4,complex)
    for j in range(4):
        a[j]=(-1)**j*np.linalg.det(np.delete(A,j,axis=1))
    return a
def fam(a,b,c):
    B=np.zeros((6,4,5),complex)
    B[0,0]=[4,-1,-1,-1,-1]; B[1,0,1:]=a; B[2,1,1:]=b; B[3,2,1:]=c
    B[4,1,0]=1; B[4,2,0]=-1; B[5,2,0]=1; B[5,3,0]=-1
    return B
def member_g(rg):
    """generic: b random in H, c = c1 + s c2 in H cap b^perp, a = cross4(b,c), T = 0 (quadratic in s)"""
    z=lambda: rg.normal(size=4)+1j*rg.normal(size=4)
    b=z(); b-=b.mean()
    Kb=null(np.array([np.ones(4),b]))            # rows: basis of {1,b}^perp (bilinear: null returns conj of vh -> check)
    Kb=np.array([k for k in Kb]);
    assert np.allclose(Kb@np.ones(4),0) and np.allclose(Kb@b,0)
    c1,c2=Kb[0],Kb[1]
    Tf=lambda s: np.sum(cross4(b,c1+s*c2)*b*(c1+s*c2))
    v=np.array([Tf(s) for s in (0,1,-1)]); A=np.array([[1,0,0],[1,1,1],[1,-1,1]]); co=np.linalg.solve(A,v)
    roots=np.roots(co[::-1]); s=roots[rg.integers(len(roots))]; c=c1+s*c2; a=cross4(b,c)
    return a,b,c
def invariants(a,b,c,rg,name,save=None):
    T3=np.sum(a*b*c); orth=[a@b,a@c,b@c,a.sum(),b.sum(),c.sum()]
    B=fam(a,b,c); Bo=onb(B); le=level_err(Bo,ntest=40)
    T=T1(embed(Bo),rg,npts=160)
    U_,S,Vh=np.linalg.svd(T[:,4,:].T,full_matrices=False); r=int((S>1e-8*S[0]).sum()); r2=int((S>1e-5*S[0]).sum())
    fo=[FO2(embed(Bo),np.random.default_rng(k),npts=160) for k in range(2)]
    e=int((defect(Bo)>1e-8).sum()); E=len(E0(Bo,rg,npts=160))
    print('%-14s dim %d lev %.0e |T|=%.0e orth %.0e e=%d dimE0=%d dimT1=%d dimOmega=%d(%d) FO2=%s'%(name,len(Bo),le,abs(T3),max(abs(np.array(orth))),e,E,len(T),r,r2,fo),flush=True)
    Om=U_[:,:r].T
    return len(T),r,fo
if __name__=='__main__':
    rg=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0)
    for k in range(6):
        a,b,c=member_g(rg); invariants(a,b,c,rg,'generic %d'%k)
    # (ii-d): b isotropic, c = b, a in {1,b,b o b}^perp
    for b in (np.array([1,1j,-1,-1j]),np.array([1,-1j,-1,1j]),):
        a=null(np.array([np.ones(4),b,b*b]))[0]; invariants(a,b,b.copy(),rg,'iso c=b')
    # degenerate span(b,c): b isotropic, c in {1,b}^perp, a = b, need sum b^2 c = 0
    b=np.array([1,1j,-1,-1j]); K=null(np.array([np.ones(4),b,b*b]))
    for cc in K: invariants(b.copy(),b,cc,rg,'a=b iso')
