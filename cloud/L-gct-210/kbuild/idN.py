import sys; sys.path.insert(0,'.')
from core import *
for which,K0 in [('drop0',[Kb[k] for k in (1,2,3)]),('drop2',[Kb[k] for k in (0,1,3)])]:
    N=E_of(K0,nsamp=30)
    for k in range(5):
        B=np.array([np.outer(r,chi(k)).ravel() for r in [np.array([1,1,1,0,0.]),np.array([0,0,0,1,1.]),np.array([0,0,0,1,-1.])]]).T
        # find combos of B in span N
        M=np.hstack([N,-B]); U,s,Vh=np.linalg.svd(M); ns=Vh[(s>1e-8).sum():].conj()
        for v in ns:
            c=v[N.shape[1]:]; c=c/c[np.argmax(abs(c))]; print(which,'weight (0,%d)'%k,'row vec coeffs [1_012, e3+e4, e3-e4]:',np.round(c,6))
