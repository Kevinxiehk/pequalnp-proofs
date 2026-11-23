import numpy as np, itertools, sys
from fractions import Fraction
def perm(A):
    A=np.asarray(A); n=A.shape[0]
    if n==0: return 1
    return sum(np.prod([A[i,p[i]] for i in range(n)]) for p in itertools.permutations(range(n)))
def Pk_rect(x,k):
    p,q=x.shape; s=0
    for R in itertools.combinations(range(p),k):
        for C in itertools.combinations(range(q),k):
            s+=perm(x[np.ix_(R,C)])
    return s
def level_poly(x):
    """sum over injections of prod(1+x) for p x q (p<=q)"""
    p,q=x.shape; y=x+1
    return sum(np.prod([y[i,f[i]] for i in range(p)]) for f in itertools.permutations(range(q),p))
def Phi(x):
    """max-minor permanents of p x (p+1) matrix: delete column j"""
    p,q=x.shape
    return np.array([perm(np.delete(x,j,axis=1)) for j in range(q)])
def orthb(B,tol=1e-9):
    M=np.asarray(B,complex).reshape(len(B),-1)
    u,s,vh=np.linalg.svd(M,full_matrices=False)
    r=int(np.sum(s>tol*s[0])); return vh[:r].reshape((r,)+np.asarray(B).shape[1:])
def nullspace(A,tol=1e-9):
    A=np.atleast_2d(A); u,s,vh=np.linalg.svd(A)
    r=int(np.sum(s>tol*max(s[0],1e-300))) if len(s) else 0
    return vh[r:].conj()
def sub_zero(B,cells):
    """subspace of span(B) vanishing on list of cells [(i,j)]; returns basis"""
    B=np.asarray(B,complex); A=np.array([[b[i,j] for b in B] for (i,j) in cells])
    N=nullspace(A.conj()).conj() if False else nullspace(A)
    # nullspace returns rows v with A v^* ... be careful: want A c = 0
    u,s,vh=np.linalg.svd(A); r=int(np.sum(s>1e-9*max(s[0],1e-300)))
    C=vh[r:].conj()   # rows c with A c = 0?  A = u s vh ; A c^T = 0 iff c^T orth to rows of vh[:r] in bilinear sense -> c = conj(vh[r:])
    return np.einsum('kc,cab->kab',C,B)
