import sys; sys.path.insert(0,'.')
from core import *
from fast import Pall
from scipy.optimize import least_squares
K0=[Kb[k] for k in (1,2,3)]; Kmat=np.array([b.ravel() for b in K0]).T
one=np.array([1,1,1,0,0.]); e34=np.array([0,0,0,1,-1.])
N0=[np.outer(one,chi(1)),np.outer(one,chi(2))]+[np.outer(e34,np.eye(5)[j]) for j in range(5)]+[np.outer(np.array([2,2,2,-3,-3.]),np.ones(5))]
Nb=np.array([b.ravel() for b in N0]).T; e=Nb.shape[1]; m=2
Y0=np.load('ext_drop0_m2_s1.npy'); Z0=np.linalg.lstsq(Nb,Y0,rcond=None)[0]; print('fit residual of saved sol in N0',np.linalg.norm(Nb@Z0-Y0))
rng=np.random.default_rng(0); npts=60
A=rng.normal(size=(npts,3))+1j*rng.normal(size=(npts,3)); Bc=rng.normal(size=(npts,m))+1j*rng.normal(size=(npts,m))
def res(z):
    Z=(z[:e*m]+1j*z[e*m:]).reshape(e,m); Y=Nb@Z
    T=(A@Kmat.T+Bc@Y.T).reshape(-1,5,5); o=Pall(T)[:,2:].ravel()
    o=np.concatenate([o,(Z.conj().T@Z-np.eye(m)).ravel()]); return np.concatenate([o.real,o.imag])
Q,_=np.linalg.qr(Z0)
z0=np.concatenate([Q.ravel().real,Q.ravel().imag])
r=least_squares(res,z0,method='lm',max_nfev=20000,xtol=1e-15,ftol=1e-15,gtol=1e-15)
Z=(r.x[:e*m]+1j*r.x[e*m:]).reshape(e,m); print('polished res',np.linalg.norm(res(r.x)))
# reduced echelon form of Z^T to read structure
M=Z.T.copy(); 
piv=[np.argmax(abs(M[0])),None]
M[0]/=M[0,piv[0]]; M[1]-=M[1,piv[0]]*M[0]; piv[1]=np.argmax(abs(M[1])); M[1]/=M[1,piv[1]]; M[0]-=M[0,piv[1]]*M[1]
np.set_printoptions(precision=5,suppress=True,linewidth=200)
print('basis coords [1x chi1, 1x chi2, E0..E4, rho]:'); print(M)
np.save('pol_drop0_m2.npy',Nb@Z)
