import numpy as np, sys
sys.path.insert(0,'.')
from closure import *
from rad import radical
import mingrowth as mg
import spaces
B=spaces.SP['ex2'](); B=B-B.mean(1,keepdims=True); Lu=orth(Phi(B))
S1=orth(np.vstack([Lu,prods(Lu,Lu)]),1e-8); R=orth(radical(S1))
m=int(sys.argv[1]); eps=float(sys.argv[2]); tl=float(sys.argv[3])
for s in range(int(sys.argv[4]),int(sys.argv[5])):
    rng=np.random.default_rng(100+s)
    L0=to_coords(R)+eps*(rng.normal(size=(9,24))+1j*rng.normal(size=(9,24)))
    nr,Lu2,sv,it=mg.run(9,m,L0=L0,seed=s,tlim=tl)
    q,t=checkP23(orth(Lu2))
    print('rad(ex2) m=%d eps %.0e seed %d res %.2e it %d |Q| %.1e |T| %.1e growth %s sv %s'%(m,eps,s,nr,it,q,t,growth(orth(Lu2),1e-7),np.array2string(sv[m-2:m+3],precision=2)),flush=True)
