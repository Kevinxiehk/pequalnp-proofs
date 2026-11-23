import sys; sys.path.insert(0,"/home/claude/work/L-gct-210/methods")
import numpy as np
from rlx import setup, search, load_space
f=sys.argv[1]
V=load_space(f); rng=np.random.default_rng(0); c=rng.normal(size=V.shape[0])+1j*rng.normal(size=V.shape[0]); x=(c@V).reshape(5,5); x/=np.linalg.norm(x)
Q,Fs,rk=setup(x)
A=np.hstack([Q,x.ravel()[:,None]]); sol=np.linalg.lstsq(A,V.T,rcond=None)[0]
print('resid',np.linalg.norm(A@sol-V.T))
Lq=sol[:-1].T; Lq=np.linalg.svd(Lq)[2][:np.linalg.matrix_rank(Lq,1e-8)]
print('L/x dim',Lq.shape[0],'isotropy',['%.1e'%np.abs(Lq@F@Lq.T).max() for F in Fs])
