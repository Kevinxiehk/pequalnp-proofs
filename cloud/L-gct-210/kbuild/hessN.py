import sys; sys.path.insert(0,'.')
from core import *
from extlm import comp, getK0
from scipy.optimize import least_squares
import itertools
def hess(t,k):
    H=np.zeros((25,25),complex)
    for i,kk in itertools.permutations(range(5),2):
        for j,l in itertools.permutations(range(5),2):
            sub=np.delete(np.delete(t,[i,kk],0),[j,l],1)
            H[5*i+j,5*kk+l]=Pk(sub,k-2)
    return H
def forms(K0,nx=6,seed=0):
    rng=np.random.default_rng(seed); Kmat,Nb=comp(K0); F=[]
    for s in range(nx):
        x=(Kmat@(rng.normal(size=len(K0))+1j*rng.normal(size=len(K0)))).reshape(5,5)
        for k in range(2,6):
            F.append(Nb.T@hess(x,k)@Nb)
    return Nb,F
def maxiso(F,e,m,seeds=6):
    best=9
    Fs=np.array(F)
    for s in range(seeds):
        rng=np.random.default_rng(s)
        def res(z):
            Z=(z[:e*m]+1j*z[e*m:]).reshape(e,m)
            R=np.einsum('ai,fab,bj->fij',Z,Fs,Z).ravel()
            G=(Z.conj().T@Z-np.eye(m)).ravel()
            o=np.concatenate([R,G]); return np.concatenate([o.real,o.imag])
        r=least_squares(res,rng.normal(size=2*e*m),method='lm',max_nfev=5000,xtol=1e-15,ftol=1e-15)
        best=min(best,np.linalg.norm(res(r.x)))
    return best
if __name__=='__main__':
    which=sys.argv[1]
    K0=getK0(which); Nb,F=forms(K0); e=Nb.shape[1]
    Fv=np.array([f[np.triu_indices(e)] for f in F]); print(which,'N dim',e,'span of Hessian forms on N:',np.linalg.matrix_rank(Fv,1e-8),'of',e*(e+1)//2)
    rad=np.linalg.svd(np.vstack(F))[1]; print('joint radical dim', e-(rad>1e-8).sum())
    for m in range(1,e):
        b=maxiso(F,e,m); print(' common isotropic subspace dim',m,'best res %.1e'%b,flush=True)
        if b>1e-6: break
