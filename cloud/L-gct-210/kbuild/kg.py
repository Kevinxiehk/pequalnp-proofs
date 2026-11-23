import sys; sys.path.insert(0,'.')
import numpy as np
from core import u, ub, chi, E_of
from hessN import hess, maxiso
from sub3w import weights
from extlm import comp
one=np.array([1,1,1,0,0.])
gens={('o',a):np.outer(one,chi(a)) for a in range(1,5)}
gens.update({('p',b):np.outer(u,chi(b)) for b in range(5)}); gens.update({('q',c):np.outer(ub,chi(c)) for c in range(5)})
for rep in [(('o',1),('p',4),('q',2),('q',3)),(('o',1),('p',1),('p',4),('q',2)),(('o',3),('p',1),('q',2),('q',3))]:
    K0=[gens[k] for k in rep]
    N=E_of(K0,nsamp=30); print(rep,'dim E',N.shape[1],weights(N))
    Kmat,Nb=comp(K0); e=Nb.shape[1]
    rng=np.random.default_rng(0); F=[]
    for s in range(5):
        x=(Kmat@(rng.normal(size=4)+1j*rng.normal(size=4))).reshape(5,5)
        for k in range(2,6): F.append(Nb.T@hess(x,k)@Nb)
    for m in range(1,e):
        b=maxiso(F,e,m,seeds=4); print('   2nd-order common isotropic dim',m,'res %.1e'%b,flush=True)
        if b>1e-6: break
