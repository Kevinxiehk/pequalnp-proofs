# structure of the zero-column-sum element x* of X in the stored defect-2 examples
import numpy as np, glob
exec(open('/home/kevxhk/work/L-gct-210/stage3/r16/ex21.py').read().split('files=')[0])
files=sorted(glob.glob('/home/kevxhk/work/L-gct-210/stage3/r10/pr2split_sol_*.npy'))+['/home/kevxhk/work/L-gct-210/stage3/r9/pr2_sol_3_8.npy']
for fn in files[:6]:
    B=np.load(fn); n=B.shape[0]; F=B.reshape(n,-1)
    zr=[n-rank(F[:,[k for k in range(20) if k//5!=r]]) for r in range(4)]; e=int(np.argmax(zr))
    A=B[:,e,:]; u,s,vh=np.linalg.svd(A.T); null=vh[rank(A):].conj().T
    X=np.delete(np.einsum('nk,nab->kab',null,B),e,axis=1)
    Cm=np.array([X[k].sum(0) for k in range(3)])            # column sums, 3 x 5
    u,s,vh=np.linalg.svd(Cm.T); z=vh[-1].conj(); xs=np.einsum('k,kab->ab',z,X)
    # single-row element of X and kernel K_0
    srow=[3-rank(np.delete(X,i,axis=1).reshape(3,-1)) for i in range(3)]; i0=int(np.argmax(srow))
    nrm=np.abs(xs).sum(1)
    print(fn.split('/')[-1],'sv(colsums)',np.round(s,6),'x* row norms',np.round(nrm/np.abs(xs).max(),4),'single-row in row',i0,
          ' x* row sums',np.round(xs.sum(1),5))
