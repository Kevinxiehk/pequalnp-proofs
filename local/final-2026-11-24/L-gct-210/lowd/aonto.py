# Level spaces L = Cg + {x(alpha)} with A onto (M free), d>=1; inspect r(g), c(g), M rank.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/lowd')
import numpy as np, d1lm2
d1lm2.MSCALE=0.2
from d1lm import rnd
import level
comps=[(k,j) for k in range(2,6) for j in range(0,k+1)]
seed=int(sys.argv[1]); starts=int(sys.argv[2]); tl=float(sys.argv[3])
out=d1lm2.run(comps,starts,seed,tl,maxit=400,nx=60,verbose=True)
for i,(f,B,sv) in enumerate(out):
    g=B[0]; print('start',i,'res %.1e'%f,'svM',sv.round(4))
    print('  r(g)',np.abs((g*g).sum(1)).round(4),' c(g)',np.abs((g*g).sum(0)).round(4), ' |g|',np.linalg.norm(g).round(3))
    np.save(f'aonto_{seed}_{i}.npy',B)
