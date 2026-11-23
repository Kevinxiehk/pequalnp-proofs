import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/dc5'); sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases')
import numpy as np
from blocksrch import ambient, run as brun
from ext import run as erun
mode=sys.argv[1]; seed=int(sys.argv[2]); rng=np.random.default_rng(seed)
f,T,_=brun(ambient([0,1,2]),4,[2,3],15,seed,25); T=T/np.abs(T).max()
if mode=='rows234': A=ambient([2,3,4])
elif mode=='cols012': A=np.transpose(ambient([0,1,2]),(0,2,1))
elif mode=='rows34': A=ambient([3,4])
best=9
for s in range(int(sys.argv[3])):
    extra=np.einsum('k,kab->ab',rng.normal(size=len(A))+1j*rng.normal(size=len(A)),A)
    fr,B=erun(list(T)+[extra],5,[2,3,4,5],1,seed*10+s,35,eps=float(sys.argv[4]))
    print(mode,'start',s,'res %.2e'%fr,flush=True); best=min(best,fr)
    if fr<1e-11: np.save(f'mix5_{mode}_{seed}.npy',B); break
print(mode,'best',best)
