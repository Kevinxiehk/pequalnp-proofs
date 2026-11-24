import sys
import numpy as np, sys, os
sys.path.insert(0, "/home/kevxhk/work/L-gct-210/methods")
from rlx import setup, search, load_space
n=5
files=sys.argv[1].split(','); seeds=[0,1]
for f in files:
    V=load_space(f); dL=V.shape[0]
    for sd in seeds:
        rng=np.random.default_rng(sd); c=rng.normal(size=dL)+1j*rng.normal(size=dL); x=(c@V).reshape(n,n); x/=np.linalg.norm(x)
        Q,Fs,rk=setup(x)
        out=[]
        for d in sorted(set([max(dL-1,1),7,8])):
            out.append('d=%d:%.0e'%(d+1,search(Fs,d,starts=int(os.environ.get('ST','3')),seed=sd)))
        print(f.split('/')[-1],'seed',sd,'dimL',dL,'gradrank',rk,'quot',Q.shape[1],'ranks',[int(np.linalg.matrix_rank(F,1e-8)) for F in Fs],' level-dim tests:',' '.join(out),flush=True)
        if dL==1: break
