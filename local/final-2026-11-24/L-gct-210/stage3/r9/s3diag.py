# Round 9 diagnostic: LM (rows/clm.py) from a known 7-dim seed perturbed by EPS; residual trajectory and Jacobian kernel at the seed.
# usage: python3 -I s3diag.py EPS SEEDINDEX
import sys, glob
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/handoff')
import numpy as np, build7, clm
from math import comb
EPS=float(sys.argv[1]); idx=int(sys.argv[2])
files=sorted(glob.glob('/home/kevxhk/work/L-gct-210/rows/clm_p4_d[456]_defect[123]_s*.npy'))
B,e=build7.build(np.load(files[idx])); print(files[idx].split('/')[-1],'dim',len(B),'defect',e,flush=True)
d=7; P=clm.Problem(5,d,'level',seed=1,N=2*comb(d+4,5))
X=B.reshape(d,-1)@P.Pi.conj().T; z0=np.linalg.solve(X[:,:d],X[:,d:]).ravel()
r,J=P.fun(z0); s=np.linalg.svd(J,compute_uv=False)
nz=(s>=1e-8*s[0]); print('at the seed: residual %.1e, Jacobian %dx%d, numerical kernel dim %d (of %d unknowns), smallest nonzero sv / max = %.1e'
      %(np.linalg.norm(r),J.shape[0],J.shape[1],J.shape[1]-nz.sum(),J.shape[1],s[nz][-1]/s[0]),flush=True)
rg=np.random.default_rng(3); z=z0+EPS*(rg.normal(size=z0.shape)+1j*rg.normal(size=z0.shape))
for k in range(8):
    z,c=clm.solve(P,z0=z,iters=25); print('after %3d iterations: residual %.2e, |z - z_seed| %.1e'%(25*(k+1),c,np.linalg.norm(z-z0)),flush=True)
