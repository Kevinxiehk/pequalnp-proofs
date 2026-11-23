import numpy as np, itertools
n = 5
# P_2, P_3 tensors on C^25 (index i*5+j); P_k(t) = (1/k!) T_k(t,...,t)
idx = [(i, j) for i in range(n) for j in range(n)]
B25 = np.zeros((25, 25))
for a, (i, j) in enumerate(idx):
    for b, (k, l) in enumerate(idx):
        if i != k and j != l:
            B25[a, b] = 1.0
T25 = np.zeros((25, 25, 25))
for a, (i, j) in enumerate(idx):
    for b, (k, l) in enumerate(idx):
        if i == k or j == l:
            continue
        for c, (p, q) in enumerate(idx):
            if p in (i, k) or q in (j, l):
                continue
            T25[a, b, c] = 1.0
# adapted orthonormal basis of C^5: column 0 = 1/sqrt5
M = np.zeros((5, 5)); M[:, 0] = 1
M[:, 1:] = np.random.RandomState(0).randn(5, 4)
F, _ = np.linalg.qr(M)
F[:, 0] = np.abs(F[:, 0])
labels = [(a, b) for a in range(5) for b in range(5) if (a, b) != (0, 0)]
E = np.array([np.outer(F[:, a], F[:, b]).ravel() for (a, b) in labels]).T  # 25 x 24
B = E.T @ B25 @ E
T = np.einsum('abc,ai,bj,ck->ijk', T25, E, E, E)
kind = np.array([0 if b == 0 else (1 if a == 0 else 2) for (a, b) in labels])  # 0 = alpha (V x 1), 1 = beta, 2 = DC


def P2(t):  # t: 25-vector
    return 0.5 * t @ B25 @ t


def P3(t):
    return np.einsum('abc,a,b,c->', T25, t, t, t) / 6


def perm(A):
    m = A.shape[0]
    return sum(np.prod([A[i, s[i]] for i in range(m)]) for s in itertools.permutations(range(m)))


if __name__ == '__main__':
    t = np.random.randn(25)
    A = t.reshape(5, 5)
    P2b = sum(perm(A[np.ix_(R, C)]) for R in itertools.combinations(range(5), 2) for C in itertools.combinations(range(5), 2))
    P3b = sum(perm(A[np.ix_(R, C)]) for R in itertools.combinations(range(5), 3) for C in itertools.combinations(range(5), 3))
    print(P2(t) - P2b, P3(t) - P3b)
    print(np.round(np.linalg.eigvalsh(B), 6))
