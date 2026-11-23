import sys; sys.path.insert(0,'.')
from core import *
rng=np.random.default_rng(5)
def Edim(basis):
    N=E_of(basis,nsamp=30); return N.shape[1],N
# generic 3-dim subspaces of K
for trial in range(3):
    A=rng.normal(size=(3,4))+1j*rng.normal(size=(3,4))
    B=[sum(A[i,k]*Kb[k] for k in range(4)) for i in range(3)]
    print('generic K3 E dim',Edim(B)[0])
for drop in range(4):
    B=[Kb[k] for k in range(4) if k!=drop]; print('coordinate K3 drop',drop,'E dim',Edim(B)[0])
# 2-dim
for drop in [(0,1),(0,2),(2,3),(1,2)]:
    B=[Kb[k] for k in range(4) if k not in drop]; print('coordinate K2 drop',drop,'E dim',Edim(B)[0])
