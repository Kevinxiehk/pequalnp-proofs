"""Checks for Lemma SL_3 (strongly level 3x5 spaces have dim <= 2).
 (T) toolbox: Y = u p^T + ubar r^T (3 x n, u = (1,w,w^2)):  P_1 = 0, P_2 = 3(p.r - sum p sum r),  P_3 = 6(e_3(p) + e_3(r)).
 (K) on DC elements Z = u lam^T + ubar mu^T with disjoint supports: p_3(Z)_j = 3(lam.lam) lam_j - 6 lam_j^3 on the support of lam.
 (X) the (q, d_N) = (1,2) configuration: residual system has no solution (symbolic identity check of the contradiction)."""
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np, itertools
from lib import Pk_rect
rng=np.random.default_rng(0); w=np.exp(2j*np.pi/3); u=np.array([1,w,w*w]); ub=u.conj()
def e(v,k): return sum(np.prod(c) for c in itertools.combinations(v,k))
err=0
for n in (4,5,6):
    for _ in range(5):
        p=rng.normal(size=n)+1j*rng.normal(size=n); r=rng.normal(size=n)+1j*rng.normal(size=n)
        Y=np.outer(u,p)+np.outer(ub,r)
        err=max(err,abs(Pk_rect(Y,1)),abs(Pk_rect(Y,2)-3*(p@r-p.sum()*r.sum())),abs(Pk_rect(Y,3)-6*(e(p,3)+e(r,3))))
print('(T) max error %.1e'%err)
# strongly level condition for Y = u p^T + ubar r^T: all 3x4 deletions level; compare with S2_j, S3_j
err=0
for _ in range(5):
    p=rng.normal(size=5)+1j*rng.normal(size=5); r=rng.normal(size=5)+1j*rng.normal(size=5); r-=r.mean(); t=p.sum()
    Y=np.outer(u,p)+np.outer(ub,r)
    for j in range(5):
        D=np.delete(Y,j,axis=1); pj=np.delete(p,j); rj=np.delete(r,j)
        err=max(err,abs(Pk_rect(D,2)-3*(p@r+r[j]*(t-2*p[j]))),abs(Pk_rect(D,3)-6*(e(pj,3)+e(rj,3))))
print('(S2_j),(S3_j) formulas for the deletions: max error %.1e'%err)
# (X): the configuration p = (pa, pb, t/2, t/2, -t/4), pa + pb = t/4, r = (0,0,nu,-nu,0): E = e_3(p)+e_3(r) and S3_c
err=0
for _ in range(5):
    t,lam,nu=rng.normal(size=3)+1j*rng.normal(size=3); pa=t/8+lam; pb=t/8-lam
    p=np.array([pa,pb,t/2,t/2,-t/4]); r=np.array([0,0,nu,-nu,0]); pi_=pa*pb
    E=e(p,3)+e(r,3); S3c=e(np.delete(p,2),3)+e(np.delete(r,2),3)
    err=max(err,abs(E-(0.75*t*pi_-t**3/16)),abs(S3c-(0.25*t*pi_-t**3/32)),abs(e(p,2)-(pi_+3*t*t/16)))
print('(X) closed forms E = (3t/4) pa pb - t^3/16, S3_c = (t/4) pa pb - t^3/32, e_2(p) = pa pb + 3t^2/16: max error %.1e'%err)
print('    => E = 0 and S3_c = 0 force pa pb = t^2/12 and pa pb = t^2/8 simultaneously: impossible for t != 0.')
