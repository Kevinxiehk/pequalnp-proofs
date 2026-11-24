import numpy as np, sys, glob, itertools
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/verify2')
import fo2lib
rng=np.random.default_rng(2); J=np.ones((5,5))
def perm5(A): return sum(np.prod([A[i,p[i]] for i in range(5)]) for p in itertools.permutations(range(5)))
for f in sorted(glob.glob('/tmp/r5_Lr3_*.npy')+glob.glob('/tmp/r5_Lr_*.npy')):
    B=np.asarray(np.load(f),dtype=complex)
    if B.ndim!=3 or B.shape[1:]!=(4,5): print(f,B.shape,'skipped'); continue
    d=len(B); X=np.zeros((d,5,5),complex); X[:,1:,:]=B
    err=0
    for _ in range(6):
        c=rng.normal(size=d)+1j*rng.normal(size=d); c/=np.linalg.norm(c); err=max(err,abs(perm5(J+np.tensordot(c,X,axes=1))-120))
    dT,r,bd,inT,iso,sg=fo2lib.fo2(X,rng)
    rowp=[np.linalg.matrix_rank(B[:,i,:],tol=1e-7) for i in range(4)]; colp=[np.linalg.matrix_rank(B[:,:,j],tol=1e-7) for j in range(5)]
    print('%-22s dim %d level err %.0e | dim T_1 %2d rank %d bound %d | row projections %s column projections %s'%(f.split('/')[-1],d,err,dT,r,bd,rowp,colp))
