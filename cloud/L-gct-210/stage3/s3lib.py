import sys, itertools
sys.path.insert(0,'/home/claude/work/L-gct-210/chief')
import numpy as np
from core import *
R5=range(5)
PAIRS=list(itertools.combinations(R5,2))
def rank(A,tol=1e-8):
    A=np.atleast_2d(np.asarray(A))
    if A.size==0: return 0
    s=np.linalg.svd(A,compute_uv=False)
    if s[0]<1e-12: return 0
    return int(np.sum(s>tol*max(1,s[0])))
def hat(B): return np.concatenate([np.ones((1,5,5),complex),B])
def sub_zero(B,cells):
    """coefficient basis (columns) of elements of span(B) vanishing on cells"""
    if len(cells)==0: return np.eye(len(B),dtype=complex)
    A=np.array([[B[k][i,j] for k in range(len(B))] for (i,j) in cells]); return nullspace(A)
def elems(B,C): return np.array([np.tensordot(C[:,a],B,1) for a in range(C.shape[1])])
def XS(B,rows=(),cols=()):
    cells=[(i,j) for i in rows for j in R5]+[(i,j) for j in cols for i in R5 if i not in rows]
    return elems(B,sub_zero(B,cells))
def ell_supporting(B,cells):
    """block K is ell-supporting iff J_K not in pi_K(L)"""
    A=np.array([[B[k][i,j] for (i,j) in cells] for k in range(len(B))])
    A2=np.concatenate([A,np.ones((1,len(cells)))])
    return rank(A2)>rank(A)
def projdim(B,cells):
    A=np.array([[B[k][i,j] for (i,j) in cells] for k in range(len(B))]); return rank(A)
def randel(B,rng):
    c=rng.normal(size=len(B))+1j*rng.normal(size=len(B)); return np.tensordot(c,B,1)
