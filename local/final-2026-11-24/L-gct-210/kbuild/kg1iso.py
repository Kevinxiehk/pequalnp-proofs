import sys; sys.path.insert(0,'.')
import numpy as np
from core import u, ub, chi
from hessN import hess
from extlm import comp
from fast import Pall
from scipy.optimize import least_squares
from iso3 import wdec
one=np.array([1,1,1,0,0.])
gens={('o',a):np.outer(one,chi(a)) for a in range(1,5)}
gens.update({('p',b):np.outer(u,chi(b)) for b in range(5)}); gens.update({('q',c):np.outer(ub,chi(c)) for c in range(5)})
K0=[gens[k] for k in (('o',1),('p',4),('q',2),('q',3))]
Kmat,Nb=comp(K0); e=Nb.shape[1]; rng=np.random.default_rng(0); F=[]
for s in range(5):
    x=(Kmat@(rng.normal(size=4)+1j*rng.normal(size=4))).reshape(5,5)
    for k in range(2,6): F.append(Nb.T@hess(x,k)@Nb)
Fs=np.array(F); m=2
for s in range(6):
    rng=np.random.default_rng(200+s)
    def res(z):
        Z=(z[:e*m]+1j*z[e*m:]).reshape(e,m)
        R=np.einsum('ai,fab,bj->fij',Z,Fs,Z).ravel(); G=(Z.conj().T@Z-np.eye(m)).ravel()
        o=np.concatenate([R,G]); return np.concatenate([o.real,o.imag])
    r=least_squares(res,rng.normal(size=2*e*m),method='lm',max_nfev=5000,xtol=1e-15,ftol=1e-15)
    Z=(r.x[:e*m]+1j*r.x[e*m:]).reshape(e,m); Y=Nb@Z
    A=rng.normal(size=(40,4+m))+1j*rng.normal(size=(40,4+m))
    T=(A@np.hstack([Kmat,Y]).T).reshape(-1,5,5); mx=np.abs(Pall(T)[:,1:]).max(0)
    print('seed',s,'iso res %.1e'%np.linalg.norm(res(r.x)),'max|P_1..5|:',np.round(mx,6),'weights:',wdec(Y))
