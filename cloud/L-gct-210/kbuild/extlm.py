"""max level extension of a fixed level space K0 inside E(K0): LM over M = span of m vectors in a complement N of K0 in E(K0)."""
import sys; sys.path.insert(0,'.')
from core import *
from fast import Pall
from scipy.optimize import least_squares
def comp(K0):
    N=E_of(K0,nsamp=30)
    Kmat=np.array([b.ravel() for b in K0]).T
    Qk,_=np.linalg.qr(Kmat); Nc=N-Qk@(Qk.conj().T@N); U,s,Vh=np.linalg.svd(Nc); Nb=U[:,:N.shape[1]-len(K0)]
    return Kmat,Nb
def run(K0,m,seed):
    rng=np.random.default_rng(seed)
    Kmat,Nb=comp(K0); e=Nb.shape[1]; d0=len(K0)
    npts=6*(d0+m)+20
    A=rng.normal(size=(npts,d0))+1j*rng.normal(size=(npts,d0)); Bc=rng.normal(size=(npts,m))+1j*rng.normal(size=(npts,m))
    A/=np.linalg.norm(A,axis=1)[:,None]; Bc/=np.linalg.norm(Bc,axis=1)[:,None]
    def res(z):
        Z=(z[:e*m]+1j*z[e*m:]).reshape(e,m); Y=Nb@Z
        T=(A@Kmat.T+Bc@Y.T).reshape(-1,5,5)
        out=Pall(T)[:,2:].ravel()
        G=Z.conj().T@Z-np.eye(m); out=np.concatenate([out,G.ravel()])
        return np.concatenate([out.real,out.imag])
    z0=rng.normal(size=2*e*m)
    r=least_squares(res,z0,method='lm',max_nfev=4000,xtol=1e-15,ftol=1e-15)
    Z=(r.x[:e*m]+1j*r.x[e*m:]).reshape(e,m)
    return np.linalg.norm(res(r.x)), Nb@Z, e
def getK0(which):
    if which.startswith('drop'):
        dr=int(which[4:]); return [Kb[k] for k in range(4) if k!=dr]
    if which=='K': return Kb
    if which=='gen':
        rr=np.random.default_rng(99); A=rr.normal(size=(3,4))+1j*rr.normal(size=(3,4)); return [sum(A[i,k]*Kb[k] for k in range(4)) for i in range(3)]
if __name__=='__main__':
    which=sys.argv[1]; m=int(sys.argv[2]); seeds=range(int(sys.argv[3]))
    K0=getK0(which)
    for s in seeds:
        res_,Y,e=run(K0,m,s); print(which,'N dim',e,'m',m,'seed',s,'res %.2e'%res_,flush=True)
        if res_<1e-8: np.save('ext_%s_m%d_s%d.npy'%(which,m,s),Y)
