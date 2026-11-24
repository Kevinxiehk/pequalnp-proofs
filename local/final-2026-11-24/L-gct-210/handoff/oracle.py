"""Reference oracle for the handoff tasks (slow, plain numpy, meant for validating fast solvers).

Conventions
  5x5 level space L:   perm(J5 + t) = 120 for all t in L   (J = all-ones).
  4x5 matrix Y, column j deleted -> 4x4 matrix Y^(j).
  deletion vector      c(Y)_j = perm(J4 + Y^(j)) - 24                (j = 0..4)
  4x5 level            sum_j c(Y)_j = 0   (equivalently sum over injective f:[4]->[5] of prod(1+Y[i,f(i)]) = 120)
  defect space         C(L') = span{ c(Y) : Y in L' }  (a subspace of 1^perp when L' is 4x5 level);  e = dim C(L')
  (d,e) space          a d-dimensional 4x5 level space with dim C(L') = e
  lift                 L = L' (in rows != r)  (+)  e_r (x) (C(L') + C*1)^perp   is a 5x5 level space of dim d + 4 - e.

Usage:  python3 oracle.py BASIS.npy [more.npy ...]
  BASIS.npy: complex array of shape (d,4,5) or (d,20): a basis of a space of 4x5 matrices,
             or shape (d,5,5)/(d,25): a basis of a space of 5x5 matrices (then only the level error is reported).
"""
import sys
import itertools
import numpy as np

PERMS4 = np.array(list(itertools.permutations(range(4))))
PERMS5 = np.array(list(itertools.permutations(range(5))))


def perm_n(M, perms):
    n = M.shape[0]
    return sum(np.prod(M[np.arange(n), p]) for p in perms)


def deletion_vector(Y):
    """c(Y)_j = perm(J4 + Y without column j) - 24."""
    out = np.zeros(5, complex)
    for j in range(5):
        cols = [c for c in range(5) if c != j]
        out[j] = perm_n(1 + Y[:, cols], PERMS4) - 24
    return out


def level_error_5x5(B, n=40, seed=1):
    rng = np.random.default_rng(seed)
    Q, _ = np.linalg.qr(B.reshape(len(B), -1).T)
    worst = 0.0
    for _ in range(n):
        x = rng.normal(size=Q.shape[1]) + 1j * rng.normal(size=Q.shape[1])
        t = (Q @ x).reshape(5, 5)
        worst = max(worst, abs(perm_n(1 + t, PERMS5) - 120))
    return worst


def analyse_4x5(B, n=120, seed=2, tol=1e-7):
    """Returns (dimension, level error, defect dimension e, singular values of the defect span)."""
    d = len(B)
    Q, _ = np.linalg.qr(B.reshape(d, -1).T)          # orthonormal basis, columns
    rng = np.random.default_rng(seed)
    C = []
    lev = 0.0
    for _ in range(n):
        x = rng.normal(size=d) + 1j * rng.normal(size=d)
        Y = (Q @ x).reshape(4, 5)
        c = deletion_vector(Y)
        lev = max(lev, abs(c.sum()))
        C.append(c)
    sv = np.linalg.svd(np.array(C), compute_uv=False)
    e = int((sv > tol * max(1.0, sv[0])).sum())
    return np.linalg.matrix_rank(B.reshape(d, -1)), lev, e, sv


def lift_to_5x5(B, r=4, tol=1e-7, n=120, seed=3):
    """Builds a basis of L = L' (rows != r) + e_r (x) (C(L') + C1)^perp."""
    d = len(B)
    Q, _ = np.linalg.qr(B.reshape(d, -1).T)
    rng = np.random.default_rng(seed)
    C = [np.ones(5, complex)]
    for _ in range(n):
        x = rng.normal(size=d) + 1j * rng.normal(size=d)
        C.append(deletion_vector((Q @ x).reshape(4, 5)))
    U, s, Vh = np.linalg.svd(np.array(C))
    rank = int((s > tol * s[0]).sum())
    free = Vh[rank:].conj()            # vectors w with sum_j c_j w_j = 0 (bilinear pairing) for all c in C + C1
    rows = [i for i in range(5) if i != r]
    out = []
    for b in B.reshape(d, 4, 5):
        t = np.zeros((5, 5), complex)
        t[rows] = b
        out.append(t)
    for w in free:
        t = np.zeros((5, 5), complex)
        t[r] = w
        out.append(t)
    return np.array(out)


if __name__ == "__main__":
    for f in sys.argv[1:]:
        B = np.load(f)
        if B.reshape(len(B), -1).shape[1] == 25:
            print(f, "5x5 space, dim", np.linalg.matrix_rank(B.reshape(len(B), -1)), "level error", level_error_5x5(B))
            continue
        B = B.reshape(len(B), 4, 5)
        dim, lev, e, sv = analyse_4x5(B)
        L = lift_to_5x5(B)
        print(f, "(d,e) = (%d,%d)" % (dim, e), "4x5 level error %.1e" % lev,
              "lift dim", np.linalg.matrix_rank(L.reshape(len(L), -1)), "lift level error %.1e" % level_error_5x5(L),
              "defect sv", np.round(sv[:5], 6))
