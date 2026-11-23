import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""tools for the defect (DI) setting: 4x5 level spaces L' with defect space C(L')."""
import numpy as np, itertools, glob
from core import *
def Cvec(Y):
    """deletion vector C(Y)_j = perm(J_4 + Y^(j)), Y (...,4,5)"""
    return np.stack([perm(1 + dele(Y, j)) for j in range(5)], -1)
def defect(B, trials=80, seed=3, tol=1e-8):
    """returns (e, basis of C(L') (rows), level error) from random points: span of C(cY) - 24 over points and scalings"""
    B = np.asarray(B, complex); rng = np.random.default_rng(seed)
    c = rng.normal(size=(trials, len(B))) + 1j * rng.normal(size=(trials, len(B)))
    Y = np.einsum('ni,iab->nab', c, B); D = Cvec(Y) - 24
    lev = np.abs(D.sum(-1)).max()
    u, s, vh = np.linalg.svd(D); e = int(np.sum(s > tol * max(1, s[0])))
    return e, vh[:e], lev, s
def onb(B):
    B = np.asarray(B, complex); u, s, vh = np.linalg.svd(B.reshape(len(B), -1), full_matrices=False)
    r = int(np.sum(s > 1e-9 * s[0])); return vh[:r].reshape(r, 4, 5)
def kernel_of(B, F):
    """subspace of span(B) on which the linear map F (applied to each basis element, returns vector) vanishes"""
    M = np.array([np.ravel(F(b)) for b in B])            # (d, n)
    u, s, vh = np.linalg.svd(M.T)                         # null space of M^T acting on coefficient vectors
    r = int(np.sum(s > 1e-8 * max(1, s[0]))) if s.size else 0
    K = vh[r:].conj().T                                   # (d, d-r)
    return np.einsum('ik,iab->kab', K, B), r
def load_rows(pattern):
    return {f.split('/')[-1]: onb(np.load(f)) for f in sorted(glob.glob('/home/claude/work/L-gct-210/rows/' + pattern))}
