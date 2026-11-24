# verify2 library: known level spaces (complex numpy bases) + linear algebra helpers.  Run with python3 -I.
import numpy as np, itertools, sys, importlib.util
def _load(path,name):
    spec=importlib.util.spec_from_file_location(name,path); m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
core=_load('/home/kevxhk/work/L-gct-210/chief/core.py','chiefcore')
ex7=_load('/home/kevxhk/work/L-gct-210/rows/exact7.py','rowsexact7')
J=np.ones((5,5))
def perm(A):
    A=np.asarray(A); m=A.shape[0]
    if m==0: return 1.0
    if A.shape[1]!=m: raise ValueError
    return sum(np.prod([A[i,p[i]] for i in range(m)]) for p in itertools.permutations(range(m)))
def spaces():
    S={k:f() for k,f in core.SP.items()}
    m=[1,2,-4,1,0]; Wb=[[1,0,0,-1,0],[4,0,1,0,-5],[2,-1,0,0,-1]]
    for c in (0,1): S['rowsLm_c%d'%c]=np.array(ex7.Lm(m,c,Wb),dtype=complex)
    w=np.exp(2j*np.pi/3); u={0:1,1:w,3:w**2}; ub={0:1,1:w**2,3:w}; B=[]
    M=np.zeros((5,5),complex)
    for i in u: M[i,0]=u[i]; M[i,3]=-u[i]
    B.append(M)
    for col in (1,4):
        M=np.zeros((5,5),complex)
        for i in ub: M[i,col]=ub[i]
        B.append(M)
    M=np.zeros((5,5),complex); M[[0,1,3],2]=1; M[2,2]=-3; B.append(M)
    for wv in ([1,-2,0,1,0],[0,1,-1,0,0],[0,1,0,0,-1]):
        M=np.zeros((5,5),complex); M[4,:]=wv; B.append(M)
    S['rows2ndkind']=np.array(B)
    S['K4']=core.K4()
    return S
def null(A,tol=1e-9):
    A=np.atleast_2d(np.asarray(A,dtype=complex))
    if A.shape[0]==0: return np.eye(A.shape[1],dtype=complex)
    u,s,vh=np.linalg.svd(A); r=int(np.sum(s>tol*max(1,s[0]))) if s.size else 0
    return vh[r:].conj().T
def rk(A,tol=1e-9):
    A=np.atleast_2d(np.asarray(A,dtype=complex))
    if A.size==0: return 0
    s=np.linalg.svd(A,compute_uv=False); return int(np.sum(s>tol*max(1,s[0])))
def hat(B):
    """basis of L^ = CJ + L as (d+1) x 25 matrix, row 0 = J; ell = coordinate 0"""
    return np.vstack([J.reshape(1,25),B.reshape(len(B),25)])
def subspace(H,cells):
    """coefficient vectors c (columns) with (c@H) vanishing on the cells"""
    idx=[5*i+j for (i,j) in cells]
    return null(H[:,idx].T)
def rnd(rng,k): return rng.normal(size=k)+1j*rng.normal(size=k)
