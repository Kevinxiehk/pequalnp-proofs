# Enumerate T1 configurations (three minimal pairs among rows 1,2,3, all ZF), check the simple S-test:
# K_S (local relations: 3 row sums + 3 pair relations restricted to S) has dim 3 and perm(tau/w) not identically 0 on K_S.
import itertools, numpy as np, random, sys
cols = range(5)
I_ = 1j
def typeI_structs():
    out = []
    for mask in range(1, 31):
        C = frozenset(m for m in cols if mask >> m & 1)
        if 0 in C: continue          # identify C with complement (relation invariant): keep the one without column 0
        w = tuple(-1 if m in C else 1 for m in cols)
        out.append(('I', C, w))
    return out
def typeII_structs():
    out = []
    for lab in itertools.product((1, 2, 3), repeat=5):
        if set(lab) != {1, 2, 3}: continue
        for eps in (1, -1):
            w = tuple({1: eps * I_, 2: 1, 3: -1}[l] for l in lab)
            out.append(('II', lab, w))
    return out
STR = typeI_structs() + typeII_structs()
print('structures', len(STR))
def rel_rows(st, S):
    # returns coefficient vectors (on rows i, j restricted to S) of the pair relation: list over S of (coef_i, coef_j)
    if st[0] == 'I':
        C = st[1]
        return [(1, -1) if m in C else (0, 0) for m in S]
    lab = st[1]
    return [(1 if lab[m] == 3 else 0, 1 if lab[m] == 2 else 0) for m in S]
def ratio_ok(w12, w13, w23):
    r = [w13[m] / (w12[m] * w23[m]) for m in cols]
    return all(abs(x - r[0]) < 1e-9 for x in r)
def stest(s12, s13, s23, S):
    # unknowns tau[i][k], i row 0..2, k in 0..2 (positions in S) -> index 3*i+k
    rows = []
    for i in range(3):
        v = np.zeros(9, complex); v[3*i:3*i+3] = 1; rows.append(v)
    for (st, a, b) in ((s12, 0, 1), (s13, 0, 2), (s23, 1, 2)):
        v = np.zeros(9, complex)
        for k, (ca, cb) in enumerate(rel_rows(st, S)):
            v[3*a+k] += ca; v[3*b+k] += cb
        rows.append(v)
    A = np.array(rows)
    rk = np.linalg.matrix_rank(A, tol=1e-9)
    if rk != 6: return False
    _, _, vh = np.linalg.svd(A)
    N = vh[6:].T   # 9x3 null basis (bilinear: no conjugation needed for a null space of A x = 0? use conj)
    N = vh[6:].conj().T
    w = [[1]*5, s12[2], [s13[2][m] for m in cols]]
    for _ in range(3):
        x = N @ np.random.randn(3) + 1j * (N @ np.random.randn(3))
        M = [[x[3*i+k] / w[i][S[k]] for k in range(3)] for i in range(3)]
        p = sum(M[0][a]*M[1][b]*M[2][c] for a, b, c in itertools.permutations(range(3)))
        if abs(p) > 1e-6: return True
    return False
random.seed(1); np.random.seed(1)
triples = list(itertools.combinations(cols, 3))
from collections import Counter
cnt = Counter(); bad = []
for s12 in STR:
    for s13 in STR:
        # w23 must be proportional to w13/w12
        q = [s13[2][m] / s12[2][m] for m in cols]
        for s23 in STR:
            if not ratio_ok(s12[2], s13[2], s23[2]): continue
            key = (s12[0], s13[0], s23[0])
            good = any(stest(s12, s13, s23, S) for S in triples)
            cnt[(key, good)] += 1
            if not good: bad.append((s12, s13, s23))
for k, v in sorted(cnt.items(), key=str): print(k, v)
print('bad', len(bad))
for b in bad[:12]: print(b)
