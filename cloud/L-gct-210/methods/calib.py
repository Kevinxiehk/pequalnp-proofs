import sys; sys.path.insert(0,"/home/claude/work/L-gct-210/methods")
import numpy as np, time
from rlx import setup, search, load_space
f=sys.argv[1]; d=int(sys.argv[2]); st=int(sys.argv[3]); nf=int(sys.argv[4])
V=load_space(f); rng=np.random.default_rng(0); c=rng.normal(size=V.shape[0])+1j*rng.normal(size=V.shape[0]); x=(c@V).reshape(5,5); x/=np.linalg.norm(x)
Q,Fs,rk=setup(x); t=time.time()
# also: check the true L/x is common isotropic (sanity of forms)
B=V.conj()  # rows
coef=np.linalg.lstsq(Q,(V - np.outer(V@x.ravel().conj()/np.vdot(x.ravel(),x.ravel()), x.ravel())).T,rcond=None)
print('residual of L in Q-span (should be small)',np.linalg.norm(Q@coef[0]-(V - np.outer(V@x.ravel().conj()/np.vdot(x.ravel(),x.ravel()), x.ravel())).T))
Lq=coef[0].T; Lq=np.linalg.svd(Lq)[2][:np.linalg.matrix_rank(Lq,1e-8)]
print('L/x dim in quotient',Lq.shape[0],'isotropy',[np.abs(Lq@F@Lq.T).max() for F in Fs])
print('best',search(Fs,d,starts=st,nfev=nf,verbose=True),'time',time.time()-t)
