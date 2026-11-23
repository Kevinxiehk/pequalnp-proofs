import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""Lemma B on real data: isometry B_m, sum B_m = -3, cross condition, S degenerate when q = 2 and N != 0, b_m in C v_m."""
import numpy as np
from core import *
from examples import *
from lmrun import Lprime
dot = lambda a, b: np.sum(a * b)
def null(M, tol=1e-9):
    u, s, vh = np.linalg.svd(M); r = int(np.sum(s > tol * max(1, s[0]))); return vh[r:].conj().T
sp = {'L080^T': Lprime(np.transpose(L080(), (0, 2, 1)), 4), 'ex1': Lprime(ex1(), 3), 'ex2': Lprime(ex2(), 3), 'ex3': Lprime(ex3(), 3),
      'fam(0.6+1.4i)': Lprime(fam(0.6 + 1.4j), 3), 'R3': Lprime(R3(), 4), 'blk42': Lprime(blk42(), 3)}
for i, B in enumerate(np.load('hits_k3.npy')): sp['LMhit%d' % i] = B
for nm, Lp in sp.items():
    S = Lp.sum(-1)                       # (3,4) row-sum vectors
    q = rank(S, 1e-8); ker = null(S.T, 1e-8)        # coefficient vectors of N
    Nb = np.einsum('ik,iab->kab', ker, Lp) if ker.shape[1] else np.zeros((0, 4, 5), complex)
    # section: pick q basis elements complementary to N
    u, s_, vh = np.linalg.svd(S.T); sec = np.einsum('ki,iab->kab', vh[:q], Lp); sig = sec.sum(-1)     # (q,4) images
    Gs = np.array([[dot(a, b) for b in sig] for a in sig]); degS = np.linalg.svd(Gs, compute_uv=False)[-1]
    err_iso = err_sum = err_cross = 0; totB = 0
    for m in range(5):
        Bm = 2 * sec[:, :, m] - sig          # rows: B_m sigma_k
        GB = np.array([[dot(a, b) for b in Bm] for a in Bm]); err_iso = max(err_iso, np.abs(GB - Gs).max()); totB = totB + Bm
        for Z in Nb:
            err_cross = max(err_cross, max(abs(dot(Z[:, m], b)) for b in Bm))
    err_sum = np.abs(totB + 3 * sig).max()
    isoN = max([abs(dot(Z[:, m], Z2[:, m])) for Z in Nb for Z2 in Nb for m in range(5)] + [0])
    msg = f'{nm:14s} (q,d)=({q},{len(Nb)}) isometry err {err_iso:.1e}, sum B_m + 3 err {err_sum:.1e}, cross err {err_cross:.1e}, N col-isotropy {isoN:.1e}, min sv of Gram(S) {degS:.2e}'
    if q == 2 and len(Nb):
        # radical u of S and b_m = B_m u ; check b_m in C v_m on active columns
        ev, evec = np.linalg.eig(Gs); c = evec[:, np.argmin(abs(ev))]; uvec = c @ sig
        worst = 0
        for m in range(5):
            bm = c @ (2 * sec[:, :, m] - sig); zm = Nb[0][:, m]
            if np.linalg.norm(zm) > 1e-8: worst = max(worst, rank(np.array([bm, zm]), 1e-7) - 1)
        msg += f' | u isotropic err {abs(dot(uvec, uvec)):.1e}, rank[b_m, v_m] - 1 on active columns: {worst}'
    print(msg)
