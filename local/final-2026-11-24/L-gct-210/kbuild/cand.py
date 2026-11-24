import sys; sys.path.insert(0,'.')
from core import *
from fast import Pall
K3=[Kb[k] for k in (1,2,3)]
one=np.array([1,1,1,0,0.]); e34=np.array([0,0,0,1,-1.])
E=lambda j: np.outer(e34,np.eye(5)[j])
c1=np.outer(one,chi(1)); c2=np.outer(one,chi(2)); c0u=np.outer(u,chi(0))
rng=np.random.default_rng(0)
def mx(B):
    L=np.array([b.ravel() for b in B]).T; A=rng.normal(size=(40,len(B)))+1j*rng.normal(size=(40,len(B)))
    return np.round(np.abs(Pall((A@L.T).reshape(-1,5,5))[:,1:]).max(0),9)
print('K3+c1', mx(K3+[c1]))
print('K3+c1+E_j', [mx(K3+[c1,E(j)]).max() for j in range(5)])
print('K3+c2', mx(K3+[c2]))
print('K3+c1+c2', mx(K3+[c1,c2]))
print('K3+u chi0', mx(K3+[c0u]))
print('K3+c1+c2+E0', mx(K3+[c1,c2,E(0)]))
print('K3+c1+E0+E1', mx(K3+[c1,E(0),E(1)]))
