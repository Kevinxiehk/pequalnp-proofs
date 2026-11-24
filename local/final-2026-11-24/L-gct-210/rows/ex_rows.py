import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/methods')
import numpy as np, itertools
from lib import *
import importlib.util
spec=importlib.util.spec_from_file_location('msp','/home/kevxhk/work/L-gct-210/methods/spaces.py'); msp=importlib.util.module_from_spec(spec); spec.loader.exec_module(msp)
rng=np.random.default_rng(1)
def rk(M,tol=1e-9):
    s=np.linalg.svd(np.atleast_2d(M),compute_uv=False); return int(np.sum(s>tol*max(s[0],1e-300))) if s.size else 0
def analyse(name,B):
    B=np.asarray(B,complex).reshape(len(B),5,5); d=rk(B.reshape(len(B),-1))
    # level check
    err=0
    for _ in range(3):
        c=rng.normal(size=len(B))+1j*rng.normal(size=len(B)); t=np.einsum('k,kab->ab',c,B)
        err=max(err,abs(level_poly(t)-120))
    print(name,'dim',d,'level err %.1e'%err)
    for tr in (0,1):
        BB=B.transpose(0,2,1) if tr else B
        out=[]
        for r in range(5):
            pr=rk(BB[:,r,:]); a=5-pr
            Lr=sub_zero(BB,[(r,j) for j in range(5)])
            ph=0
            for _ in range(3):
                c=rng.normal(size=len(Lr))+1j*rng.normal(size=len(Lr)); x=np.einsum('k,kab->ab',c,Lr)
                ph=max(ph,np.abs(Phi(np.delete(x,r,axis=0))).max())
            out.append((a,len(Lr),'%.0e'%ph))
        print('  ','cols' if tr else 'rows','(a_r, dim L_r, max|Phi|):',out)
for k,f in msp.SP.items():
    analyse(k,f())
