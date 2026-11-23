import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/reg2'); sys.path.insert(0,'/home/claude/work/L-gct-210/stage2'); sys.path.insert(0,'/home/claude/work/L-gct-210/chief')
import numpy as np, glob
from t import *
from a1 import embed, defect
from a5 import onb
from a6 import T1
from a9 import Omega, alg_closure_dim
import core
rg=np.random.default_rng(3)
def Lr(B,r):
    # subspace of span(B) (5x5) with row r = 0, returned as 4x5 matrices
    m=np.ones((5,5),bool); m[r]=False
    S=sub_supported(B,m); rows=[i for i in range(5) if i!=r]
    return S[:,rows,:]
for name,sp in core.SP.items():
    B=np.array([np.array(m,dtype=complex) for m in sp()]); d=len(B)
    for tr,Bt in (('row',B),('col',B.transpose(0,2,1))):
        out=[]
        for r in range(5):
            M=Lr(Bt,r); dm=len(M); w=rank(Bt[:,r,:])
            if dm==0: out.append('(0,-,%d)'%w); continue
            M=onb(M); Om,nT=Omega(M,rg); e=int((defect(M)>1e-6).sum())
            out.append('(dimLr=%d,e=%d,W=%d,Om=%d,T1=%d)'%(dm,e,w,len(Om),nT))
        print('%-10s dim %d %s: %s'%(name,d,tr,' '.join(out)))
