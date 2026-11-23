import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/numerics'); sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases')
import numpy as np
from core import lm_space_inner, orth, fresh_check, ext_space
B7=orth(np.load('/home/claude/work/L-gct-210/adversary/sol_r45c45_7_0.npy'))
dE,E,_=ext_space(B7); print('ext dim',dE)
rng=np.random.default_rng(int(sys.argv[1]))
for s in range(int(sys.argv[2])):
    # seed: the 7-dim space plus its extension direction (component of E orthogonal to L) + noise
    M=B7.reshape(7,-1); Ev=E.reshape(dE,-1)
    extra=Ev[np.argmax([np.linalg.norm(v-M.T@(M.conj()@v)) for v in Ev])]
    seed=np.concatenate([B7,extra.reshape(1,5,5)])
    f,B=lm_space_inner(seed,8,pert=float(sys.argv[3]),iters=300,tlimit=25,rng=rng,verbose=True)
    print(' seed',s,'res',f)
