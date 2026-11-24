"""verifyfl core: independent tools (no import from other agents' code)."""
import itertools, numpy as np
P4 = np.array(list(itertools.permutations(range(4))))
P5 = np.array(list(itertools.permutations(range(5))))
P3 = np.array(list(itertools.permutations(range(3))))
def perm(A):
    """permanent of (...,n,n) arrays, n in 3,4,5, by direct sum over permutations"""
    A = np.asarray(A); n = A.shape[-1]
    P = {3: P3, 4: P4, 5: P5}[n]
    out = np.ones(A.shape[:-2] + (len(P),), dtype=complex)
    for i in range(n):
        out = out * A[..., i, P[:, i]]
    return out.sum(-1)
def Pk(Z):
    """[P_1..P_n] of a square matrix: sums of k x k subpermanents (brute force over row/col subsets)"""
    Z = np.asarray(Z, complex); n = Z.shape[-1]; res = []
    for k in range(1, n + 1):
        tot = 0
        for R in itertools.combinations(range(n), k):
            for C in itertools.combinations(range(n), k):
                S = Z[np.ix_(R, C)]
                tot += sum(np.prod([S[i, p[i]] for i in range(k)]) for p in itertools.permutations(range(k)))
        res.append(tot)
    return np.array(res)
def dele(Y, j):
    return np.delete(Y, j, axis=-1)
def sl_res(Y):
    """strong-level residuals of 4x5 matrices Y (...,4,5): perm(J4 + Y^(j)) - 24, j=0..4"""
    Y = np.asarray(Y, complex)
    return np.stack([perm(1 + dele(Y, j)) - 24 for j in range(5)], -1)
def sl_check(B, trials=200, seed=7, scale=1.0):
    """max residual over random points of span(B), B (k,4,5)"""
    B = np.asarray(B, complex); rng = np.random.default_rng(seed)
    c = (rng.normal(size=(trials, len(B))) + 1j * rng.normal(size=(trials, len(B)))) * scale
    Y = np.einsum('ni,iab->nab', c, B)
    return np.abs(sl_res(Y)).max()
def level_check(B, trials=200, seed=7):
    B = np.asarray(B, complex).reshape(len(B), 5, 5); rng = np.random.default_rng(seed)
    c = rng.normal(size=(trials, len(B))) + 1j * rng.normal(size=(trials, len(B)))
    T = np.einsum('ni,iab->nab', c, B)
    return np.abs(perm(1 + T) - 120).max()
def rank(M, tol=1e-9):
    M = np.asarray(M, complex)
    if M.size == 0: return 0
    s = np.linalg.svd(M.reshape(len(M), -1), compute_uv=False)
    return int(np.sum(s > tol * max(1, s[0])))
tau = lambda x: np.sum(x, axis=-1)
def perm_cols(y1, y2, y3, y4):
    """claimed column formula for perm of 4x4 with sum-zero columns"""
    d = lambda a, b: tau(a * b)
    return -6 * tau(y1 * y2 * y3 * y4) + d(y1, y2) * d(y3, y4) + d(y1, y3) * d(y2, y4) + d(y1, y4) * d(y2, y3)
chi = lambda a: 1j ** (a * np.arange(4))
w3 = np.exp(2j * np.pi / 3)
