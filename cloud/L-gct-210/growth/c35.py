import numpy as np, sys, glob
sys.path.insert(0,'.'); sys.path.insert(0,'../methods')
from core import *
wgt=-125/9
def iota(Lu):
    Lu=np.asarray(Lu).reshape(-1,5,5)
    return np.concatenate([Lu.reshape(-1,25),Lu.mean(2),Lu.mean(1)],axis=1)
W=np.concatenate([np.ones(25),wgt*np.ones(10)])
# E^perp basis: z_ij = c + (25/9)(p_i+q_j)
Eperp=[]
for k in range(11):
    c=1.0 if k==0 else 0.0; p=np.zeros(5); q=np.zeros(5)
    if 1<=k<=5: p[k-1]=1
    if 6<=k<=10: q[k-6]=1
    z=c+(25/9)*(p[:,None]+q[None,:])
    Eperp.append(np.concatenate([z.ravel(),p,q]))
Eperp=np.array(Eperp)
def span(M,tol=1e-8): return orth(M,tol)
def prodspace(A,Bm):
    return span(np.array([a*b for a in A for b in Bm]))
def stab(X,tol=1e-8):
    # f with f*X subset X: for each basis x of X, f*x in X. f in C^35; linear system
    Xo=span(X); P=np.eye(35)-Xo.conj().T@Xo  # projector onto complement (Xo orthonormal rows)
    rows=[]
    for x in Xo:
        rows.append(P@np.diag(x))   # (35x35): f -> P (x*f)
    M=np.vstack(rows)
    s=np.linalg.svd(M,compute_uv=False)
    return int((s<tol*max(1,s[0])).sum()), None
def nullsp(M,tol=1e-8):
    u,s,vh=np.linalg.svd(M); r=int((s>tol*max(1,s[0])).sum()); return vh[r:].conj()
def stabbasis(X,tol=1e-8):
    Xo=span(X); P=np.eye(35)-Xo.T@Xo.conj()
    M=np.vstack([P@np.diag(x) for x in Xo])
    return nullsp(M,tol)
def analyse(Lu,name=''):
    I=iota(orth(Lu)); B=np.vstack([np.ones(35),I]); B=span(B)
    B2=prodspace(B,B)
    H=stabbasis(B2)
    j=rank(np.vstack([B2]))+11-rank(np.vstack([B2,Eperp]))
    print('%-26s l=%d dimB2=%2d h=%2d j=%2d dim(B2+E^perp)=%2d (<=%d)  2*10-h-j=%d'%(name,len(Lu),len(B2),len(H),j,rank(np.vstack([B2,Eperp])),35-len(Lu),20-len(H)-j))
    return H
if __name__=='__main__':
    import known  # prints
