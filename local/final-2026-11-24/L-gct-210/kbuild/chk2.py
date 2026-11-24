import sys; sys.path.insert(0,'.')
from iso3 import wdec, Kmat
from core import *
from fast import Pall
Y=np.load('ext_drop0_m2_s1.npy')
print('weights',wdec(Y))
L=np.hstack([Kmat,Y]); 
ux1=np.outer(u,chi(1)).ravel()
print('contains u(x)chi1:', np.linalg.matrix_rank(np.hstack([L,ux1[:,None]]),1e-6)==L.shape[1])
for j in range(5):
    E=np.outer(np.array([0,0,0,1,-1.]),np.eye(5)[j]).ravel()
    print('contains E_%d:'%j, np.linalg.matrix_rank(np.hstack([L,E[:,None]]),1e-6)==L.shape[1])
# column/row sum ranks
R=L.reshape(5,5,-1); print('rank rowsum map',np.linalg.matrix_rank(R.sum(1),1e-6),'colsum',np.linalg.matrix_rank(R.sum(0),1e-6))
rng=np.random.default_rng(0); A=rng.normal(size=(30,5))+1j*rng.normal(size=(30,5)); print('max|P|',np.abs(Pall((A@L.T).reshape(-1,5,5))[:,1:]).max())
