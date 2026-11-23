import sys; sys.path.insert(0,'.')
import numpy as np
from fast import Pall
from scipy.optimize import least_squares
d=5; e=15; seed=int(sys.argv[1]); nf=int(sys.argv[2])
rng=np.random.default_rng(seed); npts=4*d+20
A=rng.normal(size=(npts,d))+1j*rng.normal(size=(npts,d)); A/=np.linalg.norm(A,axis=1)[:,None]
def emb(Y):
    T=np.zeros((Y.shape[0],5,5),complex); T[:,:3,:]=Y.reshape(-1,3,5); return T
def res(z):
    Z=(z[:e*d]+1j*z[e*d:]).reshape(e,d); T=emb(A@Z.T); o=Pall(T)[:,1:4].ravel()
    o=np.concatenate([o,(Z.conj().T@Z-np.eye(d)).ravel()]); return np.concatenate([o.real,o.imag])
z=rng.normal(size=2*e*d)
for it in range(nf):
    r=least_squares(res,z,method='lm',max_nfev=1500,xtol=1e-15,ftol=1e-15); z=r.x
    Z=(z[:e*d]+1j*z[e*d:]).reshape(e,d)
    # singular values of P_2 Gram etc: distance to nearest 4-dim level? print residual and smallest sv of Z
    print('round',it,'res %.3e'%np.linalg.norm(res(z)),flush=True)
np.save('pol3_s%d.npy'%seed,Z)
