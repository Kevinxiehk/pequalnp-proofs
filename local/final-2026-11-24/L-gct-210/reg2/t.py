import numpy as np, itertools, glob, sys
def perm(A):
    A=np.asarray(A); n=A.shape[0]
    if n==0: return 1
    return sum(np.prod([A[i,p[i]] for i in range(n)]) for p in itertools.permutations(range(n)))
def level_poly(x):
    p,q=x.shape; y=x+1
    return sum(np.prod([y[i,f[i]] for i in range(p)]) for f in itertools.permutations(range(q),p))
def level_err(B,ntest=30,seed=0):
    rng=np.random.default_rng(seed); B=np.asarray(B); d=len(B); p,q=B.shape[1:]
    import math
    target=math.factorial(q)//math.factorial(q-p)
    e=0
    for _ in range(ntest):
        c=rng.normal(size=d)+1j*rng.normal(size=d)
        x=np.einsum('k,kab->ab',c,B)
        e=max(e,abs(level_poly(x)-target))
    return e
def rank(A,tol=1e-8):
    A=np.atleast_2d(A)
    if A.size==0: return 0
    s=np.linalg.svd(A,compute_uv=False)
    return int(np.sum(s>tol*max(s[0],1e-300))) if s[0]>1e-12 else 0
def null(A,tol=1e-8):
    """rows c with A c = 0"""
    A=np.atleast_2d(A); u,s,vh=np.linalg.svd(A)
    r=int(np.sum(s>tol*max(s[0],1e-300))) if len(s) and s[0]>1e-12 else 0
    return vh[r:].conj()
def sub_supported(B,mask):
    """subspace of span(B) of matrices vanishing outside mask (bool p x q)"""
    B=np.asarray(B,complex); d=len(B)
    A=B.reshape(d,-1)[:,~mask.ravel()].T   # (cells, d)
    if A.shape[0]==0: return B
    C=null(A)
    return np.einsum('kc,cab->kab',C,B)
def rowpart(B,rows):
    p,q=B.shape[1:]; m=np.zeros((p,q),bool); m[list(rows),:]=True; return sub_supported(B,m)
def colpart(B,cols):
    p,q=B.shape[1:]; m=np.zeros((p,q),bool); m[:,list(cols)]=True; return sub_supported(B,m)
def info(B,name=''):
    B=np.asarray(B,complex); d,p,q=B.shape
    print('==',name,'dim',rank(B.reshape(d,-1)),'level err %.1e'%level_err(B))
    print('  single-row parts',[len(rowpart(B,[i])) for i in range(p)],' single-col parts',[len(colpart(B,[j])) for j in range(q)])
    print('  row-proj ranks',[rank(B[:,i,:]) for i in range(p)],' col-proj ranks',[rank(B[:,:,j]) for j in range(q)])
    print('  two-row parts',{(i,k):len(rowpart(B,[i,k])) for i in range(p) for k in range(i+1,p)})
    print('  three-row parts',{tuple(r):len(rowpart(B,r)) for r in itertools.combinations(range(p),3)})
    print('  rowsum rank',rank(B.sum(2)),' colsum rank',rank(B.sum(1)))
if __name__=='__main__':
    for f in sys.argv[1:]:
        info(np.load(f),f)
