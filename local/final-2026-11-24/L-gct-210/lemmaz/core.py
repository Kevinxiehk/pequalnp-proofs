import numpy as np, itertools
from scipy.optimize import least_squares
_P={}
def _perms(n):
    if n not in _P: _P[n]=np.array(list(itertools.permutations(range(n))))
    return _P[n]
def perm(M):
    n=M.shape[0]; P=_perms(n)
    return np.prod(M[np.arange(n)[None,:],P],axis=1).sum()
_IDX={}
def minors(g):
    n=g.shape[0]
    if n not in _IDX:
        P=_perms(n-1); R=[];C=[]
        for i in range(n):
            for j in range(n):
                rows=np.array([r for r in range(n) if r!=i]); cols=np.array([c for c in range(n) if c!=j])
                R.append(np.broadcast_to(rows[None,:],P.shape)); C.append(cols[P])
        _IDX[n]=(np.array(R),np.array(C))
    R,C=_IDX[n]
    return np.prod(g[R,C],axis=2).sum(axis=1).reshape(n,n)
def solve(F,x0,nfev=3000):
    m=len(x0)
    def f(z):
        x=z[:m]+1j*z[m:]; r=F(x); return np.concatenate([r.real,r.imag])
    s=least_squares(f,np.concatenate([x0.real,x0.imag]),method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=nfev)
    return s.x[:m]+1j*s.x[m:], np.linalg.norm(s.fun)
