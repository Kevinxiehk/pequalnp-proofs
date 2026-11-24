import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/repr")
import numpy as np, itertools
from core import B25, T25, perm
# L = { x v^T + z e_4^T : x in C^5, z in C^5 with sum z = 0 },  v = (1, i, -1, -i, 0)
v = np.array([1, 1j, -1, -1j, 0])
basis = []
for r in range(5):
    x = np.zeros(5, complex); x[r] = 1
    basis.append(np.outer(x, v).ravel())
for r in range(4):
    z = np.zeros(5, complex); z[r] = 1; z[4] = -1
    t = np.zeros((5, 5), complex); t[:, 4] = z
    basis.append(t.ravel())
Bm = np.array(basis)  # 9 x 25, Gaussian integers
print('rank', np.linalg.matrix_rank(Bm), 'entry sums', np.abs(Bm.sum(1)).max())
# exact polarised checks (all integer arithmetic in complex128 with tiny integers -> exact)
G2 = Bm @ B25 @ Bm.T
G3 = np.einsum('abc,ia,jb,kc->ijk', T25, Bm, Bm, Bm)
print('max |P2 polar|', np.abs(G2).max(), ' max |P3 polar|', np.abs(G3).max())
# brute-force subpermanent sums at a random Gaussian-integer point (independent check)
rs = np.random.RandomState(5)
c = rs.randint(-5, 6, 9) + 1j * rs.randint(-5, 6, 9)
A = (c @ Bm).reshape(5, 5)
for k in range(1, 6):
    Pk = sum(perm(A[np.ix_(R, C)]) for R in itertools.combinations(range(5), k) for C in itertools.combinations(range(5), k))
    print('P_%d' % k, Pk)
