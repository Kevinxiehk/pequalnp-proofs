# verify2 round 4: own implementation of stage2's FO / FO2 tests (numeric, complex128).  Run with python3 -I.
import numpy as np, itertools
P3=list(itertools.permutations(range(3))); P4=list(itertools.permutations(range(4)))
def perm_small(A):
    n=A.shape[0]
    if n==3: return sum(A[0,p[0]]*A[1,p[1]]*A[2,p[2]] for p in P3)
    if n==4: return sum(A[0,p[0]]*A[1,p[1]]*A[2,p[2]]*A[3,p[3]] for p in P4)
    return sum(np.prod([A[i,p[i]] for i in range(n)]) for p in itertools.permutations(range(n)))
def cof(U):
    """25-vector of the 4x4 subpermanents: gradient of perm at U (n = 5)"""
    n=U.shape[0]; C=np.zeros((n,n),complex)
    for i in range(n):
        ri=[x for x in range(n) if x!=i]
        for j in range(n):
            cj=[x for x in range(n) if x!=j]
            C[i,j]=perm_small(U[np.ix_(ri,cj)])
    return C.reshape(n*n)
def hess(U):
    """n^2 x n^2 symmetric matrix D^2 perm at U: entry ((i,j),(k,l)) = perm of U without rows i,k and columns j,l"""
    n=U.shape[0]; Q=np.zeros((n*n,n*n),complex)
    for i in range(n):
        for k in range(n):
            if i==k: continue
            rr=[x for x in range(n) if x not in (i,k)]
            for j in range(n):
                for l in range(n):
                    if j==l: continue
                    cc=[x for x in range(n) if x not in (j,l)]
                    Q[n*i+j,n*k+l]=perm_small(U[np.ix_(rr,cc)])
    return Q
def null(A,tol=1e-9):
    u,s,vh=np.linalg.svd(A); r=int(np.sum(s>tol*max(1,s[0])))
    return vh[r:].conj().T, s     # columns span {t : A t = 0} (right singular vectors = conj of the rows of vh)
def rk(A,tol=1e-8):
    s=np.linalg.svd(A,compute_uv=False); return int(np.sum(s>tol*max(1,s[0]))), s
def fo2(B,rng,npts=60,nq=5,M=None):
    """B: (d,5,5) basis of a linear space; M: optional coefficient matrix (rows) of a subspace. Returns dim T_1, rank, bound."""
    B=np.asarray(B,dtype=complex); d=len(B); n=B.shape[1]
    if M is None: M=np.eye(d)
    J=np.ones((n,n))
    def pt():
        c=(rng.normal(size=len(M))+1j*rng.normal(size=len(M)))@M
        return J+np.tensordot(c,B,axes=1)
    A=np.array([cof(pt()) for _ in range(npts)])
    N,s=null(A)
    Q=sum((rng.normal()+1j*rng.normal())*hess(pt()) for _ in range(nq))
    G=N.T@Q@N
    r,sg=rk(G)
    # is the space itself inside T_1 and isotropic?
    Bv=B.reshape(d,n*n); inT=np.abs(A@Bv.T).max(); iso=np.abs(Bv@Q@Bv.T).max()
    return N.shape[1], r, N.shape[1]-(r+1)//2, inT, iso, sg
