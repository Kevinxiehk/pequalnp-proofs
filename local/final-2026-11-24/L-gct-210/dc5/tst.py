import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-086/smallcases')
import numpy as np, itertools
from level import Pk
w=np.exp(2j*np.pi/5); I5=np.eye(5)
def vk(k): return w**(k*np.arange(5))
V=[I5[i]-I5[4] for i in range(4)]
def test(B, trials=6, seed=0):
    B=np.array(B); rng=np.random.default_rng(seed); d=len(B)
    # rank
    r=np.linalg.matrix_rank(B.reshape(d,25),1e-9)
    worst=np.zeros(6)
    for _ in range(trials):
        x=rng.normal(size=d)+1j*rng.normal(size=d); x/=np.linalg.norm(x)
        t=np.einsum('i,iab->ab',x,B); t/=np.abs(t).max()
        worst=np.maximum(worst,np.abs(Pk(t)[0]))
    return r, np.round(worst[2:],8)
def perpV(u):  # basis of {a in V : a.u = 0}
    M=np.vstack([np.ones(5),u]); _,_,vh=np.linalg.svd(M); return vh[2:]
if __name__=='__main__':
    v=vk(1)
    for name,B in [('Vxv',[np.outer(a,v) for a in V]),
                   ('Vxv + v x (v^perp)',[np.outer(a,v) for a in V]+[np.outer(v,b) for b in perpV(v)]),
                   ('Vxv1 + Vxv2? ',[np.outer(a,v) for a in V]+[np.outer(a,vk(2)) for a in V[:1]]),
                   ('Vxv + v2perp x v2',[np.outer(a,v) for a in V]+[np.outer(b,vk(2)) for b in perpV(v)[:1]]),
                   ]:
        print(name, test(B))
