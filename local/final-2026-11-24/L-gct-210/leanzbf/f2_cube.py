# F2 cube test feasibility, orientation 1: types T0=(C,C,C),T1=(C,Q,Q),T2=(Q,C,B),T3=(B,B,C); w2=k2/k/c, w3=k3/k/c'
import itertools, numpy as np
np.random.seed(3)
for jv in (1j, -1j):
    W2 = {0: jv, 1: jv, 2: 1, 3: -1}
    W3 = {0: jv, 1: 1, 2: jv, 3: -1}
    st = {0: ('C', 'C', 'C'), 1: ('C', 'Q', 'Q'), 2: ('Q', 'C', 'B'), 3: ('B', 'B', 'C')}
    G = 1 / (1 + jv)
    res = {}
    for S in itertools.combinations_with_replacement(range(4), 3):
        rows = []; rhs = []
        # unknowns tau[i][k] (i row 0..2, k pos) index 3i+k ; plus c (index 9)
        for i in range(3):
            v = np.zeros(10, complex); v[3*i:3*i+3] = 1; v[9] = -1; rows.append(v)
        # pair 12 (rows 0,1): B12 -> row0, Q12 -> row1 ; pair 13 (rows 0,2): B13 row0, Q13 row2; pair 23 (rows1,2): B23 row1, Q23 row2
        for (a, b, pi_) in ((0, 1, 0), (0, 2, 1), (1, 2, 2)):
            v = np.zeros(10, complex)
            for k, t in enumerate(S):
                s = st[t][pi_]
                if s == 'B': v[3*a+k] += 1
                if s == 'Q': v[3*b+k] += 1
            v[9] = -G; rows.append(v)
        A = np.array(rows); rk = np.linalg.matrix_rank(A, tol=1e-9)
        _, _, vh = np.linalg.svd(A); N = vh[rk:].conj().T   # null space (10 x (10-rk))
        # restrict to c = 1 slice: find particular + homogeneous with c=0
        def perm_at(x):
            tau = x[:9]; cval = x[9]
            M = [[tau[3*i+k] / ([1]*3, [W2[t] for t in S], [W3[t] for t in S])[i][k] for k in range(3)] for i in range(3)]
            return sum(M[0][a]*M[1][b]*M[2][c] for a, b, c in itertools.permutations(range(3))), cval
        vals = []
        for _ in range(6):
            x = N @ (np.random.randn(N.shape[1]) + 1j*np.random.randn(N.shape[1]))
            if abs(x[9]) < 1e-6: continue
            x = x / x[9]
            vals.append(perm_at(x)[0])
        nonconst = max(abs(v - vals[0]) for v in vals) > 1e-6 if vals else None
        res[S] = (rk, nonconst)
    print('j =', jv, {S: r for S, r in res.items() if 0 in S})
