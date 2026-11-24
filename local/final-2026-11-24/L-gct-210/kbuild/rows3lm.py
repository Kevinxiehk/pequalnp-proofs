"""LM search for level spaces supported on rows 0..2 (3x5 block): P_4 = P_5 = 0 automatically."""
import sys; sys.path.insert(0,'.')
import numpy as np
from fast import Pall
from scipy.optimize import least_squares
def run(d,seed,cols=5):
    rng=np.random.default_rng(seed); e=3*cols; npts=4*d+20
    A=rng.normal(size=(npts,d))+1j*rng.normal(size=(npts,d)); A/=np.linalg.norm(A,axis=1)[:,None]
    def emb(Y):
        T=np.zeros((Y.shape[0],5,5),complex); T[:,:3,:cols]=Y.reshape(-1,3,cols); return T
    def res(z):
        Z=(z[:e*d]+1j*z[e*d:]).reshape(e,d)
        T=emb(A@Z.T); o=Pall(T)[:,1:4].ravel()
        o=np.concatenate([o,(Z.conj().T@Z-np.eye(d)).ravel()]); return np.concatenate([o.real,o.imag])
    r=least_squares(res,rng.normal(size=2*e*d),method='lm',max_nfev=3000,xtol=1e-15,ftol=1e-15)
    Z=(r.x[:e*d]+1j*r.x[e*d:]).reshape(e,d); return np.linalg.norm(res(r.x)),Z
if __name__=='__main__':
    d=int(sys.argv[1]); cols=int(sys.argv[3]) if len(sys.argv)>3 else 5
    for s in range(int(sys.argv[2])):
        rr,Z=run(d,s,cols); print('3x%d level d=%d seed %d res %.2e'%(cols,d,s,rr),flush=True)
        if rr<1e-9: np.save('rows3_d%d_s%d.npy'%(d,s),Z)
