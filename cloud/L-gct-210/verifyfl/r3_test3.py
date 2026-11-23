import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""Theorem FS / two-row split formulas on rows' e = 2 examples:
   single-row parts U_i (bases), identities  <u,c(Y)> = <y^i, D_i(Y)u>,  <u', D_i(Y)u> = <y^k, D_ik(Y)(u,u')>,
   and on ker gamma:  c = X X' D_ik(u,u') / (<u,u><u',u'>)   (two rows i != k carrying u, u')."""
import numpy as np, itertools
from core import *
from di_core import *
def Per5(rows): return perm(np.array(rows))
def Dvec(Y, repl):
    """vector (Per(rows of J+Y with slots in repl replaced, e_j))_j"""
    rows = [1 + Y[i] for i in range(4)]
    for i, u in repl.items(): rows[i] = u
    return np.array([Per5(rows + [np.eye(5)[j]]) for j in range(5)])
sp = load_rows('clm_p4_d5_defect2_s*.npy'); sp.update(load_rows('seed_d5_e2_t*.npy'))
rng = np.random.default_rng(4); dot = lambda a, b: np.sum(a * b)
for nm, B in sp.items():
    e, Cb, lev, sv = defect(B)
    if e != 2 or lev > 1e-8: continue
    U = {}
    for i in range(4):
        K, r = kernel_of(B, lambda Y: np.delete(Y, i, axis=0))
        if len(K): U[i] = [k[i] for k in K]
    rows_ = sorted(U)
    msg = f'{nm:26s} single-row parts in rows {[(i, len(U[i])) for i in rows_]}: '
    errs = []
    for _ in range(5):
        cf = rng.normal(size=len(B)) + 1j * rng.normal(size=len(B)); Y = np.einsum('k,kab->ab', cf, B); c = Cvec(Y) - 24
        for i in rows_:
            for u in U[i]: errs.append(abs(dot(u, c) - dot(Y[i], Dvec(Y, {i: u}))))
        if len(rows_) == 2 and len(U[rows_[0]]) == 1:
            i, k = rows_; u, up = U[i][0], U[k][0]
            errs.append(abs(dot(up, Dvec(Y, {i: u})) - dot(Y[k], Dvec(Y, {i: u, k: up}))))
    msg += 'max err of the pairing identities %.1e' % max(errs)
    if len(rows_) == 2 and len(U[rows_[0]]) == 1:
        i, k = rows_; u, up = U[i][0], U[k][0]
        L0, _ = kernel_of(B, lambda Y: Y.sum(0)); e2 = []; xs = []
        for _ in range(5):
            cf = rng.normal(size=len(L0)) + 1j * rng.normal(size=len(L0)); Y = np.einsum('k,kab->ab', cf, L0); c = Cvec(Y) - 24
            X, Xp = dot(Y[i], up), dot(Y[k], u); D2 = Dvec(Y, {i: u, k: up})
            e2.append(np.abs(c - X * Xp * D2 / (dot(u, u) * dot(up, up))).max()); xs.append((abs(X), abs(Xp), np.abs(D2).max(), np.abs(c).max()))
        msg += ' | <u,u\'>=%.0e; on ker gamma: formula err %.1e; typical |X|,|X\'|,|D_ik|,|c| = %.2g, %.2g, %.2g, %.2g' % ((abs(dot(u, up)), max(e2)) + tuple(np.mean(xs, axis=0)))
    print(msg)
