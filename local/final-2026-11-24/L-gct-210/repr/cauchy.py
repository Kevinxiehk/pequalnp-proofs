import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/repr")
import numpy as np, itertools, math
from core import perm
def Ecoef(X):
    """dict a -> E_a(X): coefficient of z^a in prod_i (1 + sum_m X[i,m] z_m), X: 5 x M"""
    n, M = X.shape
    cur = {(0,) * M: 1.0 + 0j}
    for i in range(n):
        new = dict(cur)
        for a, c in cur.items():
            for m in range(M):
                b = a[:m] + (a[m] + 1,) + a[m + 1:]
                new[b] = new.get(b, 0) + c * X[i, m]
        cur = new
    return cur
rs = np.random.RandomState(3)
for M in (1, 2, 3, 5, 7):
    X = rs.randn(5, M) + 1j * rs.randn(5, M); V = rs.randn(5, M) + 1j * rs.randn(5, M)
    EX, EV = Ecoef(X), Ecoef(V)
    rhs = sum(math.factorial(5 - sum(a)) * np.prod([math.factorial(k) for k in a]) * EX[a] * EV[a] for a in EX)
    lhs = perm(np.ones((5, 5)) + X @ V.T)
    print(M, abs(lhs - rhs) / abs(lhs))
