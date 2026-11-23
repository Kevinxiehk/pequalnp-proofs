"""Second-order bound for level spaces containing a given DC level element g (or a space D):
   L subset E(D), L totally isotropic for B_2 = Hess P_2 and H_k(x) = Hess P_k(x), x in D, k = 3,4,5.
   S2(D) := dim D + max dim of a common isotropic subspace of E(D)/D  >= dim L."""
import sys; sys.path.insert(0,'.')
import numpy as np, itertools
from core import Pk, grad, u, ub, chi
from fast import Pall
from scipy.optimize import least_squares
def hess(t,k):
    H=np.zeros((25,25),complex)
    for i,kk in itertools.permutations(range(5),2):
        for j,l in itertools.permutations(range(5),2):
            H[5*i+j,5*kk+l]=Pk(np.delete(np.delete(t,[i,kk],0),[j,l],1),k-2)
    return H
def setup(Dbasis,nx=None,seed=0):
    rng=np.random.default_rng(seed); d=len(Dbasis)
    Dm=np.array([b.ravel() for b in Dbasis]).T
    xs=[Dbasis[0]] if d==1 else [ (Dm@(rng.normal(size=d)+1j*rng.normal(size=d))).reshape(5,5) for _ in range(nx or 3*d)]
    rows=[grad(x,k).ravel() for x in xs for k in range(1,6)]
    U,s,Vh=np.linalg.svd(np.array(rows)); r=(s>1e-9*s[0]).sum(); E=Vh[r:].conj().T   # 25 x dimE
    # complement of D inside E
    Q,_=np.linalg.qr(Dm); Ec=E-Q@(Q.conj().T@E); U2,s2,_=np.linalg.svd(Ec,full_matrices=False); Nb=U2[:,:E.shape[1]-d]
    F=[Nb.T@hess(np.ones((5,5)),2)@Nb]
    for x in xs:
        for k in (3,4,5): F.append(Nb.T@hess(x,k)@Nb)
    return E.shape[1],Nb,np.array(F)
def iso(Fs,m,seed,Z0=None,nfev=4000):
    e=Fs.shape[1]; rng=np.random.default_rng(seed)
    def res(z):
        Z=(z[:e*m]+1j*z[e*m:]).reshape(e,m)
        R=np.einsum('ai,fab,bj->fij',Z,Fs,Z).ravel(); G=(Z.conj().T@Z-np.eye(m)).ravel()
        o=np.concatenate([R,G]); return np.concatenate([o.real,o.imag])
    z0=rng.normal(size=2*e*m)/np.sqrt(e) if Z0 is None else np.concatenate([Z0.ravel().real,Z0.ravel().imag])
    r=least_squares(res,z0,method='lm',max_nfev=nfev,xtol=1e-15,ftol=1e-15)
    Z=(r.x[:e*m]+1j*r.x[e*m:]).reshape(e,m); return np.linalg.norm(res(r.x)),Z
def report(name,Dbasis,ms,seeds=3):
    dE,Nb,Fs=setup(Dbasis); e=Nb.shape[1]; d=len(Dbasis)
    ranks=[np.linalg.matrix_rank(f,1e-8) for f in Fs[:4]]
    rad=e-(np.linalg.svd(np.vstack(list(Fs)),compute_uv=False)>1e-8).sum()
    print('%s: d=%d dim E=%d, forms on E/D (dim %d): ranks(B2,H3,H4,H5 at first x)=%s joint radical %d'%(name,d,dE,e,ranks,rad),flush=True)
    for m in ms:
        best=min(iso(Fs,m,s)[0] for s in range(seeds))
        print('   common isotropic dim m=%d: best res %.1e  -> %s'%(m,best,'EXISTS: level dim %d not excluded at 2nd order'%(d+m) if best<1e-9 else 'not found (bound dim L <= %d)'%(d+m-1)),flush=True)
        if best>1e-9: break
if __name__=='__main__':
    w3=np.exp(2j*np.pi/3); e=np.eye(5)
    types={
     'T1 u(e0-e1)^T [ex1/ex2 DC type]': [np.outer(u,e[0]-e[1])],
     'T2 generic element of K': [np.outer(u,chi(1)+0.7*chi(4))+np.outer(ub,(0.3+0.5j)*chi(2)-1.1*chi(3))],
     'T3 u chi1^T': [np.outer(u,chi(1))],
     'T8 (e0-e1)(chi1+chi2)^T [2-row]': [np.outer(e[0]-e[1],chi(1)+chi(2))],
    }
    which=sys.argv[1]; ms=[int(x) for x in sys.argv[2].split(',')]
    for name,Db in types.items():
        if name.startswith(which): report(name,Db,ms,seeds=int(sys.argv[3]) if len(sys.argv)>3 else 3)
