import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/repr")
import numpy as np
from core import B, T, kind
N = 24
# unknowns: X (N*N, X[m,i] at m*N+i), c2, c3
rows = []
# quadric: sum_m B[m,j] X[m,i] + B[i,m] X[m,j] - c2 B[i,j] = 0
for i in range(N):
    for j in range(i, N):
        r = np.zeros(N * N + 2)
        for m in range(N):
            r[m * N + i] += B[m, j]
            r[m * N + j] += B[i, m]
        r[N * N] = -B[i, j]
        rows.append(r)
A2 = np.array(rows)
rows = []
for i in range(N):
    for j in range(i, N):
        for k in range(j, N):
            r = np.zeros(N * N + 2)
            for m in range(N):
                r[m * N + i] += T[m, j, k]
                r[m * N + j] += T[i, m, k]
                r[m * N + k] += T[i, j, m]
            r[N * N + 1] = -T[i, j, k]
            rows.append(r)
A3 = np.array(rows)
for name, A in [('P3 only', A3), ('P2 and P3', np.vstack([A2, A3])), ('P2 only', A2)]:
    s = np.linalg.svd(A, compute_uv=False)
    nul = A.shape[1] - np.sum(s > 1e-9 * s[0])
    print(name, 'nullity', nul, 'smallest sv', s[-nul - 3:][::-1][:6] if nul < A.shape[1] else None)
A = A3
U, s, Vt = np.linalg.svd(A)
nul = A.shape[1] - np.sum(s > 1e-9 * s[0])
K = Vt[-nul:]
np.save('lieP3.npy', K)
for v in K:
    X = v[:N * N].reshape(N, N)
    print('c2', v[N * N], 'c3', v[N * N + 1], 'rank X', np.linalg.matrix_rank(X, 1e-8))
