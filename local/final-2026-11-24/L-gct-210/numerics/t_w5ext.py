import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/numerics')
from core import *
W=orth(weight_w5()); A=sumzero_ambient()
e=int(sys.argv[1]); seed=int(sys.argv[2]); ns=int(sys.argv[3])
rng=np.random.default_rng(seed)
for s in range(ns):
    seedB=rng.normal(size=(e,5,5))+1j*rng.normal(size=(e,5,5))
    f,B=lm_space(seedB,3+e,fixed=W,ambient=A,iters=300,tlimit=40,rng=rng,verbose=True)
    if f<1e-9:
        print(report(f'W5+{e}',B)); np.save(f'/home/kevxhk/work/L-gct-210/numerics/S{3+e}_w5ext_s{seed}_{s}.npy',B); break
