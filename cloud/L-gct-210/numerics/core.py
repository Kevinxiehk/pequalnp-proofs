"""numerics core for L-gct-210 (5x5 level spaces). Reuses L-gct-086 smallcases/level.py."""
import sys, time
sys.path.insert(0, '/home/claude/work/L-gct-086/smallcases')
import numpy as np
from math import comb
from level import Pk, Pk_grad, construction_2n3, dc_basis, check_exact

N = 5


def orth(B):
    """orthonormal basis (rows) of span of B (d,n,n) -> (d',n,n)"""
    M = np.asarray(B, complex).reshape(len(B), -1)
    u, s, vh = np.linalg.svd(M, full_matrices=False)
    r = np.sum(s > 1e-9 * s[0])
    return vh[:r].reshape(r, N, N)


def fresh_check(B, trials=60, seed=12345):
    """max |P_k|, k=1..5, at random unit points of span(orthonormalised B)."""
    Q = orth(B)
    rng = np.random.default_rng(seed)
    x = rng.normal(size=(trials, len(Q))) + 1j * rng.normal(size=(trials, len(Q)))
    x /= np.linalg.norm(x, axis=1, keepdims=True)
    T = np.einsum('ri,iab->rab', x, Q)
    return np.abs(Pk(T)[:, 1:]).max()


# ---- decomposition t = alpha_i + beta_j + gamma (+ const) ----
def proj_parts(t):
    t = np.asarray(t)
    m = t.mean()
    a = t.mean(1) - m
    b = t.mean(0) - m
    g = t - a[:, None] - b[None, :] - m
    return m, a, b, g


def invariants(B):
    """dim, d = dim(L ∩ DC), r = rank of (alpha,beta) projection, ra, rb ranks of row/col parts."""
    Q = orth(B)
    D = len(Q)
    AB = []
    A = []
    Bc = []
    for t in Q:
        m, a, b, g = proj_parts(t)
        AB.append(np.concatenate([[m], a, b]))
        A.append(a)
        Bc.append(b)
    AB = np.array(AB); A = np.array(A); Bc = np.array(Bc)
    rk = lambda M: int(np.sum(np.linalg.svd(M, compute_uv=False) > 1e-8)) if M.size else 0
    r = rk(AB)
    return dict(dim=D, r=r, d=D - r, ra=rk(A), rb=rk(Bc))


def ext_space(B, nsamp=300, seed=0, tol=1e-9):
    """first-order extension space E(L) = {t : DP_k(l)[t] = 0 for all l in L, k=1..5}.
    returns (dimE, orthonormal basis of E (rows, n n), singular values)"""
    Q = orth(B)
    D = len(Q)
    rng = np.random.default_rng(seed)
    xs = rng.normal(size=(nsamp, D)) + 1j * rng.normal(size=(nsamp, D))
    xs /= np.linalg.norm(xs, axis=1, keepdims=True)
    T = np.einsum('ri,iab->rab', xs, Q)
    P, G = Pk_grad(T)
    rows = G[:, 1:].reshape(-1, N * N)
    u, s, vh = np.linalg.svd(rows)
    rk = np.sum(s > tol * s[0])
    E = vh[rk:].conj()  # null space: rows . v = 0  (G . t, bilinear, no conj on t)
    return N * N - rk, E.reshape(-1, N, N), s


def grass_tangent(B, nsamp=None, seed=0, tol=1e-8):
    """dim of first-order deformations of L as a level space: phi in Hom(L, C^25/L) with
    DP_k(l)[phi(l)] = 0 for all l (polynomial identity in l). Returns dim of the deformation
    space (excluding nothing; symmetries contribute 0 since perms are discrete, scaling acts
    trivially on Grassmannian)."""
    Q = orth(B)
    D = len(Q)
    M = Q.reshape(D, -1)
    # complement basis
    u, s, vh = np.linalg.svd(M)
    C = vh[D:].conj()  # (25-D, 25)  orthogonal complement (conj so that M C^H... ) fine
    # careful: we want a complement of span rows of M; vh[D:] rows orthogonal (hermitian) to M rows
    C = vh[D:]
    nsamp = nsamp or (comb(D + 4, 5) + 30)
    rng = np.random.default_rng(seed)
    xs = rng.normal(size=(nsamp, D)) + 1j * rng.normal(size=(nsamp, D))
    xs /= np.linalg.norm(xs, axis=1, keepdims=True)
    T = np.einsum('ri,iab->rab', xs, Q)
    P, G = Pk_grad(T)  # G (R,6,5,5)
    GC = np.einsum('rkab,pab->rkp', G[:, 1:], C.reshape(-1, N, N))  # R K p
    J = np.einsum('ri,rkp->rkip', xs, GC).reshape(nsamp * 5, -1)
    s = np.linalg.svd(J, compute_uv=False)
    rk = np.sum(s > tol * s[0])
    return J.shape[1] - rk, s


# ---- LM over a Grassmannian chart around a seed ----
def lm_space_inner(seedB, D, fixed=None, ambient=None, iters=200, tlimit=60, rng=None, pert=0.0,
             verbose=False, nextra=10):
    """Find a D-dim level space L = span(fixed) + span(new), new rows varying in a chart
    around seed. seedB: (D-f, n, n) initial new vectors (can be random). fixed: (f,n,n) or None.
    ambient: (m,n,n) orthonormal ambient basis for new vectors (default all 25 minus P_1 const?).
    Returns (res, basis)."""
    rng = rng or np.random.default_rng(0)
    if ambient is None:
        ambient = np.eye(N * N).reshape(N * N, N, N).astype(complex)
    Am = np.asarray(ambient, complex).reshape(len(ambient), -1)
    m = len(Am)
    fixed = np.zeros((0, N, N), complex) if fixed is None else np.asarray(fixed, complex)
    f = len(fixed)
    e = D - f
    # coordinates of seed in ambient (least squares)
    S = np.asarray(seedB, complex).reshape(e, -1)
    coef = np.linalg.lstsq(Am.T, S.T, rcond=None)[0].T  # e x m
    # orthonormal chart: Q rows: first e span coef rows, rest complement
    u, s, vh = np.linalg.svd(coef)
    Q = vh  # m x m unitary, first e rows span seed coords
    X = pert * (rng.normal(size=(e, m - e)) + 1j * rng.normal(size=(e, m - e)))
    nsamp = comb(D + 4, 5) + nextra
    xs = rng.normal(size=(nsamp, D)) + 1j * rng.normal(size=(nsamp, D))
    xs /= np.linalg.norm(xs, axis=1, keepdims=True)
    Cq = (Q[e:] @ Am).reshape(m - e, N, N)
    Fq = fixed

    def newvecs(X):
        return ((np.hstack([np.eye(e), X]) @ Q) @ Am).reshape(e, N, N)

    def res(X, jac=True):
        Bn = newvecs(X)
        allB = np.concatenate([Fq, Bn])
        T = np.einsum('ri,iab->rab', xs, allB)
        if not jac:
            return Pk(T)[:, 1:].reshape(-1)
        P, G = Pk_grad(T)
        GC = np.einsum('rkab,pab->rkp', G[:, 1:], Cq)
        Jm = np.einsum('ri,rkp->rkip', xs[:, f:], GC)
        R, K = GC.shape[:2]
        return P[:, 1:].reshape(-1), Jm.reshape(R * K, -1)

    t0 = time.time()
    lam = 1e-3
    r, Jm = res(X)
    fv = np.linalg.norm(r)
    for it in range(iters):
        if time.time() - t0 > tlimit:
            break
        H = Jm.conj().T @ Jm
        g = Jm.conj().T @ r
        try:
            step = np.linalg.solve(H + lam * np.diag(np.diag(H).real + 1e-12), -g)
        except np.linalg.LinAlgError:
            break
        Xn = X + step.reshape(X.shape)
        fn = np.linalg.norm(res(Xn, False))
        if fn < fv:
            X = Xn; lam = max(lam / 3, 1e-14)
            r, Jm = res(X); fv = fn
        else:
            lam *= 4
            if lam > 1e10:
                break
        if fv < 1e-14:
            break
    Bout = np.concatenate([Fq, newvecs(X)])
    if verbose:
        print(f'   lm: res {fv:.2e} it {it} |X| {np.linalg.norm(X):.2e} t {time.time()-t0:.1f}s', flush=True)
    return fv, Bout


def polish(B, iters=60, tlimit=60):
    """Newton-polish a whole approximate level space (all vectors move)."""
    Q = orth(B)
    return lm_space(Q, len(Q), iters=iters, tlimit=tlimit, rounds=3)


def L080():
    return np.array(construction_2n3(5), dtype=complex)


def sumzero_ambient():
    """orthonormal basis of the 24-dim space of sum-zero 5x5 matrices"""
    M = np.eye(25) - np.ones((25, 25)) / 25
    u, s, vh = np.linalg.svd(M)
    return vh[:24].reshape(24, N, N).astype(complex)


def dc_ambient():
    B = dc_basis(5).reshape(16, -1)
    q, _ = np.linalg.qr(B.T)
    return q.T.reshape(16, N, N).astype(complex)


def weight_w5():
    from tangent import weight_space
    return weight_space(5, [1, 2, 3, 4, 0], [1, 2, 0, 4, 3], 30, [2, 3, 4])


def report(name, B):
    inv = invariants(B)
    fc = fresh_check(B)
    dE, E, s = ext_space(B)
    return f'{name}: {inv} fresh={fc:.1e} extdim={dE}'


def lm_space(seedB, D, fixed=None, ambient=None, iters=200, tlimit=60, rng=None, pert=0.0,
             verbose=False, rounds=8, oversample=2.0):
    """outer loop: re-chart at the current solution with fresh oversampled points each round."""
    rng = rng or np.random.default_rng(0)
    t0 = time.time()
    f0 = 0 if fixed is None else len(fixed)
    if ambient is None:
        ambient = sumzero_ambient()
    if fixed is not None and len(fixed):
        Fm = orth(fixed).reshape(len(fixed), -1)
        Am = np.asarray(ambient, complex).reshape(len(ambient), -1)
        Am = Am - (Am @ Fm.conj().T) @ Fm
        u, s, vh = np.linalg.svd(Am, full_matrices=False)
        ambient = vh[:np.sum(s > 1e-9)].reshape(-1, N, N)
    cur = np.asarray(seedB, complex)
    best = (np.inf, None)
    per = max(20, iters // rounds)
    for rd in range(rounds):
        nextra = int(oversample * comb(D + 4, 5))
        left = tlimit - (time.time() - t0)
        if left <= 0:
            break
        fv, B = lm_space_inner(cur, D, fixed=fixed, ambient=ambient, iters=per, tlimit=left,
                               rng=rng, pert=pert if rd == 0 else 0.0, nextra=nextra)
        new = B[f0:]
        # orthonormalise new vectors (keeps span(fixed)+span(new))
        M = new.reshape(len(new), -1)
        q, _ = np.linalg.qr(M.T)
        cur = q.T.reshape(-1, N, N)
        fc = fresh_check(B, trials=40, seed=rd + 7)
        if verbose:
            print(f'   round {rd}: res {fv:.2e} fresh {fc:.2e} t {time.time()-t0:.1f}s', flush=True)
        if fc < best[0]:
            best = (fc, B)
        if fc < 1e-12:
            break
        if rd >= 2 and fc > 1e-2:
            break
    return best
