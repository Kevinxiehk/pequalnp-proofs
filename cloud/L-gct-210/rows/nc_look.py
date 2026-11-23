import sys,glob; sys.path.insert(0,'/home/claude/work/L-gct-210/rows')
import numpy as np
from clm import *
def rk(M,tol=1e-6):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol).sum())
def nullsp(M,tol=1e-6):
    u,s,vh=np.linalg.svd(M); r=int((s>tol).sum()); return vh[r:].conj().T
def look(f,k):
    Z=np.load(f); d=Z.shape[0]            # (d,4,5)
    nb=list(range(k)); S=[j for j in range(5) if j not in nb]
    T=Z[:,:,S].reshape(d,-1); dT=rk(T)
    # kernel K: elements with zero S-columns
    N=nullsp(T.T); K=np.einsum('ad,aij->dij',N,Z) if N.shape[1] else np.zeros((0,4,5))
    out=['d=%d k=%d dimT=%d dimK=%d'%(d,k,dT,K.shape[0])]
    # single column parts
    for n in range(5):
        oth=[j for j in range(5) if j!=n]; out.append('X%d=%d'%(n,d-rk(Z[:,:,oth].reshape(d,-1))))
    # single row parts
    for i in range(4):
        oth=[r for r in range(4) if r!=i]; out.append('U%d=%d'%(i,d-rk(Z[:,oth,:].reshape(d,-1))))
    # row projections rank, column projections rank
    out.append('rowrk '+str([rk(Z[:,i,:]) for i in range(4)])); out.append('colrk '+str([rk(Z[:,:,j]) for j in range(5)]))
    # pairs of columns equal: dim{y_a=y_b}
    out.append('eqS '+str([d-rk((Z[:,:,a]-Z[:,:,b])) for a in S for b in S if a<b]))
    out.append('eqN '+str([d-rk((Z[:,:,a]-Z[:,:,b])) for a in nb for b in nb if a<b]))
    # row sums rank, col sums rank
    out.append('rowsumrk %d colsumrk %d'%(rk(Z.sum(2)),rk(Z.sum(1))))
    return ' '.join(out)
if __name__=='__main__':
    k=int(sys.argv[2])
    for f in sorted(glob.glob(sys.argv[1])): print(f.split('/')[-1],look(f,k))
