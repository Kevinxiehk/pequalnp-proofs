# Round 9 diagnostic 2: is the stall of LM at known 7-dim spaces caused by a positive-dimensional SMOOTH family (cured by random linear
# slices through the seed, k = numerical kernel dim) or by a NON-REDUCED solution set (stall persists)?  usage: python3 -I s3diag2.py EPS IDX
import sys, glob
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np, build7, clm
from math import comb
EPS=float(sys.argv[1]); idx=int(sys.argv[2])
files=sorted(glob.glob('/home/kevxhk/work/L-gct-210/rows/clm_p4_d[456]_defect[123]_s*.npy'))
B,e=build7.build(np.load(files[idx])); d=7; P=clm.Problem(5,d,'level',seed=1,N=2*comb(d+4,5))
X=B.reshape(d,-1)@P.Pi.conj().T; z0=np.linalg.solve(X[:,:d],X[:,d:]).ravel()
r,J=P.fun(z0); u,s,vh=np.linalg.svd(J); k=int((s<1e-8*s[0]).sum())+J.shape[1]-len(s)
rg=np.random.default_rng(5); S=rg.normal(size=(k,len(z0)))+1j*rg.normal(size=(k,len(z0))); S/=np.linalg.norm(S,axis=1)[:,None]
w=np.sqrt(np.trace(J.conj().T@J).real/len(z0))
print(files[idx].split('/')[-1],'kernel dim',k,'; slices through the seed added with weight %.1e'%w,flush=True)
class Sl:
    def __init__(s_,P): s_.P=P; s_.rng=P.rng; s_.nvar=P.nvar
    def fun(s_,z,jac=True):
        if jac:
            r,J=s_.P.fun(z); return np.concatenate([r,w*(S@(z-z0))]),np.concatenate([J,w*S])
        return np.concatenate([s_.P.fun(z,jac=False),w*(S@(z-z0))])
Q=Sl(P); z=z0+EPS*(rg.normal(size=z0.shape)+1j*rg.normal(size=z0.shape))
for it in range(6):
    z,c=clm.solve(Q,z0=z,iters=8); print('after %2d iterations: residual (with slices) %.2e, level residual %.2e, |z - z_seed| %.1e'%(8*(it+1),c,np.linalg.norm(P.fun(z,jac=False)),np.linalg.norm(z-z0)),flush=True)
