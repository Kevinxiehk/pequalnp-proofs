# Round 16: structure of the 14 stored 5-dim 4x5 level spaces of shape single-row (2,1,0,0) / row projections (2,2,2,2):
# N = X (+) e_e (x) Z; X = rows != e (3-dim 3x5, rows in planes, defect <= 2) has a single-row element. Report: e, X's kernel dims K_i, single-row
# row, dim c(X), defect of X, and the column structure.
import numpy as np, glob, itertools, sys
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16')
def rank(A,tol=1e-6):
    s=np.linalg.svd(np.atleast_2d(A),compute_uv=False); return int((s>tol*max(1,s[0])).sum()) if s.size else 0
def sig(M,m,cols):
    tot=0
    for R in itertools.combinations(range(M.shape[0]),m):
        for C in itertools.permutations(cols,m): tot+=np.prod([M[R[k],C[k]] for k in range(m)])
    return tot
def delv(x): return np.array([[sig(x,m,[c for c in range(5) if c!=j]) for j in range(5)] for m in (1,2,3)])
files=sorted(glob.glob('/home/kevxhk/work/L-gct-210/stage3/r10/pr2split_sol_*.npy'))+['/home/kevxhk/work/L-gct-210/stage3/r9/pr2_sol_3_8.npy']
rg=np.random.default_rng(0)
for fn in files:
    B=np.load(fn); n=B.shape[0]; F=B.reshape(n,-1)
    # single-row parts
    zr=[]
    for r in range(4):
        idx=[k for k in range(20) if k//5!=r]; zr.append(n-rank(F[:,idx]))
    e=int(np.argmax(zr))
    # X = complement: elements of N with row e = 0
    A=B[:,e,:]; u,s,vh=np.linalg.svd(A.T); null=vh[rank(A):].conj().T   # combos with row e zero
    X=np.einsum('nk,nab->kab',null,B); X=np.delete(X,e,axis=1)   # (3,3,5)
    FX=X.reshape(X.shape[0],-1)
    K=[X.shape[0]-rank(X[:,i,:]) for i in range(3)]
    srow=[X.shape[0]-rank(np.delete(X,i,axis=1).reshape(X.shape[0],-1)) for i in range(3)]
    Rc=np.array([X[k].sum(0) for k in range(X.shape[0])]); dR=rank(Rc)
    Q=rg.normal(size=(30,X.shape[0]))+1j*rg.normal(size=(30,X.shape[0])); xs=np.einsum('nk,kab->nab',Q,X)
    D=np.concatenate([delv(x) for x in xs]); dD=rank(D,1e-6)
    # kernel coplanarity: dims of K_i and of their sum
    Kb=[]
    for i in range(3):
        A=X[:,i,:]; u,s,vh=np.linalg.svd(A.T); Kb.append(vh[rank(A):].conj().T)
    dsum=rank(np.concatenate(Kb,1)) if all(b.shape[1] for b in Kb) else -1
    print('%-22s zr=%s e=%d dimX=%d K=%s dimSumK=%d singleRow(X)=%s dim c(X)=%d defect=%d'%(fn.split('/')[-1],zr,e,X.shape[0],K,dsum,srow,dR,dD))
