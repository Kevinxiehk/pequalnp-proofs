import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np, itertools, glob
from t import *
from a1 import *
def onb(B):
    d=len(B); sh=B.shape[1:]; u,s,vh=np.linalg.svd(B.reshape(d,-1),full_matrices=False); r=int((s>1e-8*s[0]).sum()); return vh[:r].reshape((r,)+sh)
rg=np.random.default_rng(5)
for f in sys.argv[1:]:
    B=np.load(f)
    if B.shape[1:]!=(4,5): print(f,B.shape,'skip'); continue
    B=onb(B); d=len(B)
    le=level_err(B)
    ps=phirank(B); ds=defect(B)
    n,rho,bd=FO2(embed(B),rg)
    print('%-40s dim %d lev %.0e | Phi sv %s | defect sv %s | rows %s cols %s | T1 %d rk %d FO2 %d'%(f.split('/')[-1],d,le,np.array2string(ps,precision=1),np.array2string(ds,precision=1),[len(rowpart(B,[i])) for i in range(4)],[len(colpart(B,[j])) for j in range(5)],n,rho,bd))
