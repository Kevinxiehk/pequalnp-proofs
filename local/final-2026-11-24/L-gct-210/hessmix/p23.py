# LM: subspaces Y of V (u-coords) with P2=P3=0 (exact u-forms), Grassmannian chart.  usage: p23.py l seed nstarts
import sys, time; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/hessmix')
from hk import *
from scipy.optimize import least_squares
l=int(sys.argv[1]); seed=int(sys.argv[2]); ns=int(sys.argv[3])
rng=np.random.default_rng(seed)
RowS=np.kron(np.eye(5),np.ones((1,5)))  # 5x25: row sums
ColS=np.kron(np.ones((1,5)),np.eye(5))
iu2=np.triu_indices(l)
idx3=[(a,b,c) for a in range(l) for b in range(a,l) for c in range(b,l)]
I3=tuple(np.array(idx3).T)
def eqs(Y):
    R=Y@RowS.T; C=Y@ColS.T
    E2=(Y@Y.T-(5/9)*(R@R.T+C@C.T))[iu2]
    T=np.einsum('ap,bp,cp->abc',Y,Y,Y)-(1/9)*(np.einsum('ap,bp,cp->abc',R,R,R)+np.einsum('ap,bp,cp->abc',C,C,C))
    return np.concatenate([E2,T[I3]])
for st in range(ns):
    t0=time.time()
    Z=rng.normal(size=(24,24))+1j*rng.normal(size=(24,24)); Qm,_=np.linalg.qr(Z)
    B0=Qm[:,:l].T@VB; N=Qm[:,l:].T@VB   # rows in C^25 (inside V)
    def Yof(x):
        X=(x[:len(x)//2]+1j*x[len(x)//2:]).reshape(l,24-l); return B0+X@N
    def res(x):
        e=eqs(Yof(x)); return np.concatenate([e.real,e.imag])
    x0=0.3*rng.normal(size=2*l*(24-l))
    r=least_squares(res,x0,method='lm',max_nfev=20000,xtol=1e-15,ftol=1e-15)
    Y=Yof(r.x); Yo=np.linalg.qr(Y.T)[0].T
    e=eqs(Yo)  # residual on orthonormalised basis
    # back to t-coordinates: t = Phi^{-1}(u): u=g-(3/2)a -> t = g - (2/3) a_u ; a_u = AB part of u
    T=[]
    for y in Yo:
        m,a_,b_,g=parts(y.reshape(5,5)); T.append(g-(2/3)*ab(a_,b_))
    T=np.array(T)
    P=Pk(np.einsum('k,kij->ij',rng.normal(size=l)+1j*rng.normal(size=l),T)[None])[0]
    print('l=%d start %d: res(orth) %.1e  nfev %d  %.0fs  |P2|,|P3| at random pt %.1e %.1e  |P4|,|P5| %.1e %.1e'%(l,st,np.abs(e).max(),r.nfev,time.time()-t0,abs(P[2]),abs(P[3]),abs(P[4]),abs(P[5])),inv(T) if np.abs(e).max()<1e-9 else '')
    sys.stdout.flush()
    if np.abs(e).max()<1e-9: np.save('p23_l%d_s%d_%d.npy'%(l,seed,st),T)
