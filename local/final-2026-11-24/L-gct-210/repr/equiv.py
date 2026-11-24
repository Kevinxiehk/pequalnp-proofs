import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/repr")
import numpy as np, itertools
from core import B25, T25, P2, P3
lam = -16.0 / 9
# check u-identity
rs = np.random.RandomState(1)
t = rs.randn(5, 5); t -= t.mean()
al = t.mean(1); be = t.mean(0)
a = al[:, None] + be[None, :]
g = t - a
u = g - 1.5 * a
au = -1.5 * a
lhs2 = 2 * P2(t.ravel()); rhs2 = lam * (au ** 2).sum() + (g ** 2).sum()
lhs3 = 1.5 * P3(t.ravel()); rhs3 = lam * (au ** 3).sum() + 3 * (au ** 2 * g).sum() + 3 * (au * g * g).sum() + (g ** 3).sum()
print('identity check', lhs2 - rhs2, lhs3 - rhs3)

cyc = {'e': [], '2': [(0, 1)], '22': [(0, 1), (2, 3)], '3': [(0, 1, 2)], '32': [(0, 1, 2), (3, 4)], '4': [(0, 1, 2, 3)], '5': [(0, 1, 2, 3, 4)]}


def permmat(cs):
    p = list(range(5))
    for c in cs:
        for k in range(len(c)):
            p[c[k]] = c[(k + 1) % len(c)]
    M = np.zeros((5, 5))
    for i in range(5):
        M[p[i], i] = 1
    return M


# W basis: 25-dim matrices with sum zero; use orthonormal basis of 1^perp in C^25
one = np.ones(25) / 5
Wb = np.linalg.svd(np.eye(25) - np.outer(one, one))[0][:, :24]


def action(s, tt, transp):
    Ps, Pt = permmat(cyc[s]), permmat(cyc[tt])
    cols = []
    for k in range(25):
        X = np.zeros(25); X[k] = 1; X = X.reshape(5, 5)
        Y = Ps @ X @ Pt.T
        if transp:
            Y = Y.T
        cols.append(Y.ravel())
    return np.array(cols).T


def eigdecomp(Mact):
    A = Wb.T @ Mact @ Wb
    m = 1
    while not np.allclose(np.linalg.matrix_power(A, m), np.eye(24)):
        m += 1
    # projectors onto eigenspaces: P_k = (1/m) sum_j zeta^{-jk} A^j
    spaces = {}
    pw = [np.linalg.matrix_power(A, j) for j in range(m)]
    for k in range(m):
        z = np.exp(2j * np.pi * k / m)
        P = sum(z ** (-j) * pw[j] for j in range(m)) / m
        r = np.linalg.matrix_rank(P, 1e-8)
        if r:
            U, s, _ = np.linalg.svd(P)
            spaces[k] = Wb @ U[:, :r]  # 25 x r complex, columns basis of eigenspace (in C^25 coordinates)
    return m, spaces


def forms(spaces, m):
    keys = sorted(spaces)
    Qf = {}; Cf = {}
    for a in keys:
        for b in keys:
            if b < a or (a + b) % m:
                continue
            M = spaces[a].T @ B25 @ spaces[b]
            Qf[(a, b)] = M
    for a, b, c in itertools.combinations_with_replacement(keys, 3):
        if (a + b + c) % m:
            continue
        Tn = np.einsum('xyz,xi,yj,zk->ijk', T25, spaces[a], spaces[b], spaces[c])
        Cf[(a, b, c)] = Tn
    return Qf, Cf


def neq(kv, Qf, Cf):
    e = 0
    for (a, b), M in Qf.items():
        if np.abs(M).max() < 1e-9:
            continue
        e += kv[a] * (kv[a] + 1) // 2 if a == b else kv[a] * kv[b]
    for (a, b, c), Tn in Cf.items():
        if np.abs(Tn).max() < 1e-9:
            continue
        if a == b == c:
            e += kv[a] * (kv[a] + 1) * (kv[a] + 2) // 6
        elif a == b:
            e += kv[a] * (kv[a] + 1) // 2 * kv[c]
        elif b == c:
            e += kv[b] * (kv[b] + 1) // 2 * kv[a]
        else:
            e += kv[a] * kv[b] * kv[c]
    return e


if __name__ == '__main__':
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    types = list(cyc)
    results = []
    seen = set()
    elems = [(s, tt, 0) for s in types for tt in types] + [(s, 'e', 1) for s in types]
    for (s, tt, tr) in elems:
        if (s, tt, tr) == ('e', 'e', 0):
            continue
        key = tuple(sorted([s, tt])) + (tr,)
        if key in seen:
            continue
        seen.add(key)
        m, sp = eigdecomp(action(s, tt, tr))
        Qf, Cf = forms(sp, m)
        keys = sorted(sp)
        dims = [sp[k].shape[1] for k in keys]
        best = None
        for kv in itertools.product(*[range(d + 1) for d in dims]):
            if sum(kv) != K:
                continue
            kd = dict(zip(keys, kv))
            unk = sum(kd[k] * (sp[k].shape[1] - kd[k]) for k in keys)
            e = neq(kd, Qf, Cf)
            ex = unk - e
            if best is None or ex > best[0]:
                best = (ex, kd, unk, e)
        results.append((best[0], (s, tt, tr), m, dict(zip(keys, dims)), best[1], best[2], best[3]))
    results.sort(key=lambda r: -r[0])
    for r in results[:15]:
        print(r)
