"""Level-space tool for perm(J+t), n <= 6.

(n-k)! P_k(T) = (-1)^n sum_S (-1)^{|S|} |S|^{n-k} e_k(u(S)),  u(S)_i = sum_{j in S} T_ij
(Ryser applied to J + sT and expanded in s).  perm(J+sT) = sum_k (n-k)! P_k(T) s^k.
"""
import itertools, math
from fractions import Fraction
import numpy as np

_masks = {}


def masks(n):
    if n not in _masks:
        M = np.array([[(S >> j) & 1 for j in range(n)] for S in range(2 ** n)], dtype=float)
        _masks[n] = M
    return _masks[n]


def esym(u, kmax):
    """u: (..., n) -> (..., kmax+1) elementary symmetric polys."""
    sh = u.shape[:-1]
    E = np.zeros(sh + (kmax + 1,), dtype=complex)
    E[..., 0] = 1
    for i in range(u.shape[-1]):
        for k in range(kmax, 0, -1):
            E[..., k] = E[..., k] + u[..., i] * E[..., k - 1]
    return E


def Pk(T):
    """T: (R,n,n) complex -> (R, n+1) array of P_0..P_n."""
    T = np.asarray(T, dtype=complex)
    if T.ndim == 2:
        T = T[None]
    R, n, _ = T.shape
    M = masks(n)  # (2^n, n)
    U = np.einsum('rij,sj->rsi', T, M)  # (R,2^n,n)
    E = esym(U, n)  # (R,2^n,n+1)
    sz = M.sum(1)
    sign = (-1.0) ** (n + sz)
    out = np.zeros((R, n + 1), dtype=complex)
    for k in range(n + 1):
        w = sign * sz ** (n - k) if k < n else sign * 1.0
        out[:, k] = (E[:, :, k] * w[None, :]).sum(1) / math.factorial(n - k)
    return out


def Pk_grad(T):
    """returns P (R,n+1) and G (R,n+1,n,n) with G[r,k,a,b] = dP_k/dT_ab."""
    T = np.asarray(T, dtype=complex)
    R, n, _ = T.shape
    M = masks(n)
    U = np.einsum('rij,sj->rsi', T, M)
    E = esym(U, n)
    sz = M.sum(1)
    sign = (-1.0) ** (n + sz)
    P = np.zeros((R, n + 1), dtype=complex)
    G = np.zeros((R, n + 1, n, n), dtype=complex)
    W = np.zeros((n + 1, 2 ** n))
    for k in range(n + 1):
        W[k] = (sign * sz ** (n - k) if k < n else sign) / math.factorial(n - k)
        P[:, k] = (E[:, :, k] * W[k][None, :]).sum(1)
    for a in range(n):
        Ua = np.delete(U, a, axis=2)
        Ea = esym(Ua, n - 1)  # (R,2^n,n)
        for k in range(1, n + 1):
            # dP_k/dU_a(S) = W[k,S] e_{k-1}(u_{-a})
            coef = Ea[:, :, k - 1] * W[k][None, :]  # (R,2^n)
            G[:, k, a, :] = coef @ M  # sum over S with b in S
    return P, G


# ---------- exact check (Fractions / Gaussian rationals via python complex of Fractions not
# available; use sympy-free exact integer/Fraction arithmetic for rational bases) ----------

def Pk_exact(T):
    """T: list of lists of Fractions/ints (or sympy numbers). Returns [P_0..P_n] exactly."""
    n = len(T)
    out = []
    for k in range(n + 1):
        tot = 0
        for R in itertools.combinations(range(n), k):
            for C in itertools.permutations(range(n), k):
                if list(C) != sorted(C) and False:
                    pass
            # sum over k-subsets of rows and injective maps rows->cols
            for C in itertools.permutations(range(n), k):
                p = 1
                for i, c in zip(R, C):
                    p = p * T[i][c]
                    if p == 0:
                        break
                tot = tot + p
        out.append(tot)
    return out


def check_exact(basis, n, simplify=None):
    """basis: list of n x n matrices with exact entries. Certifies P_k == 0 on span for all
    k = 1..n by evaluating the homogeneous degree-k polynomial P_k(sum a_i B_i) on all
    a in N^d with |a| = k (a unisolvent set for homogeneous forms of degree k).
    Returns list of (k, number of nonzero evaluations)."""
    d = len(basis)
    res = []
    for k in range(1, n + 1):
        bad = 0
        for comp in compositions(k, d):
            T = [[sum(comp[i] * basis[i][a][b] for i in range(d)) for b in range(n)]
                 for a in range(n)]
            v = Pk_exact(T)[k]
            if simplify is not None:
                v = simplify(v)
            if v != 0:
                bad += 1
        res.append((k, bad))
    return res


def compositions(k, d):
    if d == 1:
        yield (k,)
        return
    for i in range(k + 1):
        for rest in compositions(k - i, d - 1):
            yield (i,) + rest


def check_numeric(basis, n, trials=20, rng=None):
    rng = rng or np.random.default_rng(0)
    B = np.array(basis, dtype=complex)
    d = len(B)
    worst = np.zeros(n + 1)
    for _ in range(trials):
        x = rng.normal(size=d) + 1j * rng.normal(size=d)
        x /= np.linalg.norm(x)
        T = np.einsum('i,iab->ab', x, B)
        P = np.abs(Pk(T)[0])
        worst = np.maximum(worst, P)
    return worst


def construction_2n3(n):
    """basis of the L-gct-080 space (last row/col), exact integers."""
    basis = []
    for j in range(n - 2):  # last row: e_j - e_{n-2}
        T = [[0] * n for _ in range(n)]
        T[n - 1][j] = 1
        T[n - 1][n - 2] = -1
        basis.append(T)
    for i in range(n - 1):  # last column y_i, corner -y_i
        T = [[0] * n for _ in range(n)]
        T[i][n - 1] = 1
        T[n - 1][n - 1] = -1
        basis.append(T)
    return basis


def dc_basis(n):
    """basis of doubly centred matrices: E_ij - E_in - E_nj + E_nn, i,j<n-1."""
    out = []
    for i in range(n - 1):
        for j in range(n - 1):
            T = np.zeros((n, n))
            T[i, j] = 1; T[i, n - 1] = -1; T[n - 1, j] = -1; T[n - 1, n - 1] = 1
            out.append(T)
    return np.array(out)


if __name__ == '__main__':
    # sanity: P_k for J+sT vs brute permanents at n=4
    rng = np.random.default_rng(1)
    for n in range(2, 7):
        T = rng.normal(size=(n, n))
        P = Pk(T)[0]
        Pe = Pk_exact([[Fraction(int(round(1000 * v)), 1000) for v in row] for row in T])
        print(n, np.max(np.abs(P - np.array([float(v) for v in Pe]))))
