import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2')
import numpy as np, glob
from t import *
from a1 import Phi
def onb(B):
    d=len(B); sh=B.shape[1:]; u,s,vh=np.linalg.svd(B.reshape(d,-1),full_matrices=False); r=int((s>1e-8*s[0]).sum()); return vh[:r].reshape((r,)+sh)
def rk(A,tol): 
    s=np.linalg.svd(A,compute_uv=False); return int((s>tol*s[0]).sum())
fs=sorted(glob.glob('../rows/rc45.npy')+glob.glob('../rows/clm_p4_d6_*.npy')+glob.glob('../rows/nc_d6_*.npy')+glob.glob('../rows/seed_d6_*.npy'))
for f in fs:
    B=onb(np.load(f))
    rr=[rk(B[:,i,:],1e-5) for i in range(4)]; cc=[rk(B[:,:,j],1e-5) for j in range(5)]
    rs=[np.array2string(np.linalg.svd(B[:,i,:],compute_uv=False)[3:],precision=1) for i in range(4)]
    print('%-32s rows %s cols %s | row sv[3:] %s'%(f.split('/')[-1],rr,cc,' '.join(rs)))
