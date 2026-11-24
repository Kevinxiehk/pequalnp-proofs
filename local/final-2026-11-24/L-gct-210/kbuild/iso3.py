import sys; sys.path.insert(0,'.')
from hessN import *
from fast import Pall
K0=getK0('drop0'); Nb,F=forms(K0); e=Nb.shape[1]; Fs=np.array(F)
Kmat=np.array([b.ravel() for b in K0]).T
rowvecs={0:[np.array([1,1,1,0,0.]),np.array([0,0,0,1,0.]),np.array([0,0,0,0,1.])],1:[u],2:[ub]}
def wdec(Y):
    out=[]
    for a in range(3):
      for k in range(5):
        B=np.array([np.outer(r,chi(k)).ravel() for r in rowvecs[a]]).T
        P=B@np.linalg.pinv(B); nrm=np.linalg.norm(P@Y)
        if nrm>1e-6: out.append(((a,k),round(float(nrm),3)))
    return out
m=int(sys.argv[1])
for s in range(int(sys.argv[2])):
    rng=np.random.default_rng(100+s)
    def res(z):
        Z=(z[:e*m]+1j*z[e*m:]).reshape(e,m)
        R=np.einsum('ai,fab,bj->fij',Z,Fs,Z).ravel(); G=(Z.conj().T@Z-np.eye(m)).ravel()
        o=np.concatenate([R,G]); return np.concatenate([o.real,o.imag])
    r=least_squares(res,rng.normal(size=2*e*m),method='lm',max_nfev=5000,xtol=1e-15,ftol=1e-15)
    Z=(r.x[:e*m]+1j*r.x[e*m:]).reshape(e,m); Y=Nb@Z
    if np.linalg.norm(res(r.x))>1e-8: print('seed',s,'no iso'); continue
    A=rng.normal(size=(40,3+m))+1j*rng.normal(size=(40,3+m))
    T=(A@np.hstack([Kmat,Y]).T).reshape(-1,5,5); mx=np.abs(Pall(T)[:,1:]).max(0)
    # also: the iso subspace's projection onto sub-blocks
    print('seed',s,'iso res %.1e'%np.linalg.norm(res(r.x)),'max|P_1..5| on K3+M:',np.round(mx,4),'weights of M:',wdec(Y))
