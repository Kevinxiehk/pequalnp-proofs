# r=8 (resp. r=7 calibration) P2,P3-only feasibility in u-coordinates: Y_A = {rho/5 (x) 1 + Gamma rho}, Y_B = {1 (x) sigma/5 + Delta sigma}
import sys, time; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/hessmix')
from hk import *
from scipy.optimize import least_squares
sys.path.insert(0,'/home/kevxhk/work/L-gct-086/smallcases')
from level import dc_basis
rb=int(sys.argv[1]); seed=int(sys.argv[2]); ns=int(sys.argv[3])
rng=np.random.default_rng(seed)
Ub=np.linalg.qr(dc_basis(5).reshape(16,-1).T)[0].T  # 16x25 orthonormal DC basis
RowS=np.kron(np.eye(5),np.ones((1,5))); ColS=np.kron(np.ones((1,5)),np.eye(5))
E4=np.array([np.eye(5)[k]-np.eye(5)[4] for k in range(4)])  # basis of C^5_0
l=4+rb
iu2=np.triu_indices(l); idx3=np.array([(a,b,c) for a in range(l) for b in range(a,l) for c in range(b,l)]).T
nvar=2*(64+16*rb+(0 if rb==4 else 4*rb))
def build(x):
    z=x[:len(x)//2]+1j*x[len(x)//2:]
    G=z[:64].reshape(16,4); H=z[64:64+16*rb].reshape(16,rb)
    if rb==4: S=E4
    else:
        W=z[64+16*rb:].reshape(rb,4); S=W@E4   # sigma basis (rb x 5), sum zero
    YA=np.array([np.outer(E4[k],np.ones(5)).ravel()/5 for k in range(4)])+G.T@Ub
    YB=np.array([np.outer(np.ones(5),S[k]).ravel()/5 for k in range(rb)])+H.T@Ub
    return np.vstack([YA,YB]),S
def eqs(Y):
    R=Y@RowS.T; C=Y@ColS.T
    E2=(Y@Y.T-(5/9)*(R@R.T+C@C.T))[iu2]
    T=np.einsum('ap,bp,cp->abc',Y,Y,Y)-(1/9)*(np.einsum('ap,bp,cp->abc',R,R,R)+np.einsum('ap,bp,cp->abc',C,C,C))
    return np.concatenate([E2,T[tuple(idx3)]])
def res(x):
    Y,S=build(x); e=eqs(Y)
    if rb<4:  # keep S well-conditioned: penalise S S^H - I mildly via fixing: add gauge eqs S[:, :rb] = I-ish
        g=(S@np.linalg.pinv(E4))[:, :rb]-np.eye(rb); e=np.concatenate([e,g.ravel()])
    out=np.concatenate([e.real,e.imag])
    return np.concatenate([out,np.zeros(max(0,nvar-len(out)))])
for st in range(ns):
    t0=time.time(); x0=0.5*rng.normal(size=nvar)
    r=least_squares(res,x0,method='lm',max_nfev=6000,xtol=1e-15,ftol=1e-15,gtol=1e-15)
    Y,S=build(r.x); Yo=np.linalg.qr(Y.T)[0].T; e=np.abs(eqs(Yo)).max()
    print('rB=%d start %d: res %.1e (orthonormalised %.1e) nfev %d %.0fs  minsv(Y) %.2e'%(rb,st,np.linalg.norm(r.fun),e,r.nfev,time.time()-t0,sv(Y)[-1]),flush=True)
