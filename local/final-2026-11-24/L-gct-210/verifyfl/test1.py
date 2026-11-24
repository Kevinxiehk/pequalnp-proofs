import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
"""TASK 1: reduction L = F_r (+) L', L' strongly level -- numerical check on the known 7-dim examples."""
import numpy as np, sys
from core import *
from examples import *
def Frow(r):
    return np.array([E(r, j) - E(r, 4) for j in range(4)])
def nullspace(M, tol=1e-9):
    u, s, vh = np.linalg.svd(M); r = int(np.sum(s > tol * max(1, s[0]))); return vh[r:].conj().T
def analyse(name, B):
    B = np.asarray(B, complex).reshape(len(B), 5, 5); k = rank(B)
    print(f'== {name}: dim {k}, level err {level_check(B):.1e}')
    for tr in (0, 1):
        Bt = np.transpose(B, (0, 2, 1)) if tr else B
        for r in range(5):
            if rank(np.concatenate([Bt, Frow(r)])) != k: continue
            # all elements have row-r sum zero?
            rs = np.abs(Bt[:, r, :].sum(-1)).max()
            # L' = L cap {row r = 0}
            Ns = nullspace(Bt[:, r, :].T)          # coefficient vectors c with sum_i c_i B_i[r,:] = 0
            Lp = np.einsum('ik,iab->kab', Ns, Bt)
            Lp4 = np.delete(Lp, r, axis=1)          # 4x5 matrices
            dimLp = rank(Lp4)
            # (q,d)
            S = Lp4.sum(-1); q = rank(S)
            err = sl_check(Lp4)
            # P_1..P_4 of deletions at a random point (independent of perm(J+.) check)
            rng = np.random.default_rng(1); c = rng.normal(size=len(Lp4)) + 1j * rng.normal(size=len(Lp4))
            Y = np.einsum('i,iab->ab', c, Lp4)
            pk = max(np.abs(Pk(dele(Y, j))).max() for j in range(5))
            print(f'   free {"col" if tr else "row"} {r}: rowsum_r max {rs:.1e}; dim L\' = {dimLp} (dim L - 4 = {k-4}); '
                  f'(q,d) = ({q},{dimLp-q}); strong-level err {err:.1e}; max|P_k(Y^(j))| {pk:.1e}')
for n, f in EX.items(): analyse(n, f())
# negative control: L9^T contains free row 4 but is not level; its L' = chi_1 (x) C^5 must fail strong levelness
B = L9T(); print('L9T: level err %.2e (not level expected)' % level_check(B))
Lp = np.array([np.outer(chi(1), np.eye(5)[c]) for c in range(5)])
Y = np.einsum('i,iab->ab', np.arange(1, 6) * (1 + 0.3j), Lp)
print('  chi_1 (x) C^5: P_k of deletion 0:', np.round(Pk(dele(Y, 0)), 8))
# identity used in the reduction: perm(J + y + e_5 w^T) = perm(J + y) + sum_j w_j C_j,  C_j = perm((J+y) minus row 5, col j)
rng = np.random.default_rng(5); mx = 0
for _ in range(20):
    y = rng.normal(size=(5, 5)) + 1j * rng.normal(size=(5, 5)); wv = rng.normal(size=5) + 1j * rng.normal(size=5)
    A = 1 + y; lhs = perm(A + np.outer(np.eye(5)[4], wv)); C = np.array([perm(np.delete(A[:4], j, axis=1)) for j in range(5)])
    mx = max(mx, abs(lhs - perm(A) - wv @ C), abs(perm(A) - A[4] @ C))
print('row-expansion identity max err %.1e' % mx)
# converse: F_4 (+) L' level for strongly level L' : random element
for n in ('ex1', 'R3'):
    B = EX[n]()
print('done')
