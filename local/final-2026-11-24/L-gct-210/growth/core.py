import sys, itertools
sys.path.insert(0,'/home/kevxhk/work/L-gct-086/smallcases')
import numpy as np, level
n=5; N=25
# basis of U = sum-zero 5x5 (24 vectors in C^25), orthonormal-ish
_E=np.eye(N)
_one=np.ones(N)/np.sqrt(N)
_P=np.eye(N)-np.outer(_one,_one)
_u,_s,_vh=np.linalg.svd(_P)
UB=_u[:,:24].T.copy()   # 24 x 25 real orthonormal basis of sum-zero
def to_coords(M):  # M: (m,25) sum-zero -> (m,24)
    return np.asarray(M).reshape(-1,N)@UB.T
def to_mat(c):     # (m,24) -> (m,25)
    return np.asarray(c)@UB
def decomp(T):
    T=np.asarray(T).reshape(-1,n,n); c=T.mean(axis=(-1,-2),keepdims=True)
    al=T.mean(axis=-1)-c[...,0]; be=T.mean(axis=-2)-c[...,0]
    g=T-c-al[...,:,None]-be[...,None,:]
    return c[...,0,0],al,be,g
def Phi(T):  # t -> u = g - 1.5(al_i+be_j)
    c,al,be,g=decomp(T); return (g-1.5*(al[:,:,None]+be[:,None,:])).reshape(-1,N)
def PhiInv(Um):
    c,al,be,g=decomp(Um); return (g-(2/3)*(al[:,:,None]+be[:,None,:])).reshape(-1,N)
def RC(u):
    u=np.asarray(u).reshape(-1,n,n); return u.sum(2),u.sum(1)
# forms in u-coordinates
def Qf(u,v):
    R,C=RC(u); R2,C2=RC(v)
    return (np.asarray(u).reshape(-1,N)*np.asarray(v).reshape(-1,N)).sum(1)-(5/9)*((R*R2).sum(1)+(C*C2).sum(1))
def Tf(u,v,w):
    R,C=RC(u); R2,C2=RC(v); R3,C3=RC(w)
    return (np.asarray(u).reshape(-1,N)*np.asarray(v).reshape(-1,N)*np.asarray(w).reshape(-1,N)).sum(1)-(1/9)*((R*R2*R3).sum(1)+(C*C2*C3).sum(1))
def G(u):
    c,al,be,g=decomp(u); return (g-(16/9)*(al[:,:,None]+be[:,None,:])).reshape(-1,N)
def Ginv(h):
    c,al,be,g=decomp(h); return (g-(9/16)*(al[:,:,None]+be[:,None,:])).reshape(-1,N)
def h(u,v):
    u=np.asarray(u).reshape(-1,N); v=np.asarray(v).reshape(-1,N)
    R,C=RC(u); R2,C2=RC(v)
    return u*v-(1/9)*((R*R2)[:,:,None]+(C*C2)[:,None,:]).reshape(-1,N)
def prod(u,v):  # u∘v in u-coordinates (sum-zero matrices)
    return Ginv(h(u,v))
# Gram matrix of Q on UB
QM=np.array([[Qf(UB[a],UB[b])[0] for b in range(24)] for a in range(24)])
def rank(M,tol=1e-8):
    M=np.asarray(M); 
    if M.size==0: return 0
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol*max(1,s[0])).sum())
def growth(Lu,tol=1e-8):
    """Lu: (l,25) basis in u-coords. returns dim L, dim L∘L, dim(L+L∘L)"""
    Lu=np.asarray(Lu).reshape(-1,N); l=len(Lu)
    P=[prod(Lu[a],Lu[b])[0] for a in range(l) for b in range(a,l)]
    P=np.array(P)
    return rank(Lu,tol),rank(P,tol),rank(np.vstack([Lu,P]),tol)
def orth(M,tol=1e-9):
    M=np.asarray(M); u,s,vh=np.linalg.svd(M,full_matrices=False); r=int((s>tol*max(1,s[0])).sum()); return vh[:r]
def checkP23(Lu):
    Lu=np.asarray(Lu).reshape(-1,N); l=len(Lu)
    q=max(abs(Qf(Lu[a],Lu[b])[0]) for a in range(l) for b in range(l))
    t=max(abs(Tf(Lu[a],Lu[b],Lu[c])[0]) for a in range(l) for b in range(l) for c in range(l))
    return q,t
def rand_iso(l,rng):
    """random l-dim Q-isotropic subspace of U (u-coords, (l,25))"""
    # diagonalize QM (real symmetric)
    lam,O=np.linalg.eigh(QM)
    # z = sqrt(lam) O^T y ; isotropic in z: pairs z_{2k}= i z_{2k+1}
    A=rng.normal(size=(24,24))+1j*rng.normal(size=(24,24)); K=(A-A.T)*0.5
    from scipy.linalg import expm
    Orth=expm(K)  # complex orthogonal
    Z=np.zeros((12,24),dtype=complex)
    for k in range(12): Z[k,2*k]=1; Z[k,2*k+1]=1j
    Z=Z@Orth.T
    # y = O diag(1/sqrt(lam)) z
    Y=(Z/np.sqrt(lam.astype(complex)))@O.T
    C=rng.normal(size=(l,12))+1j*rng.normal(size=(l,12))
    return to_mat(C@Y)
