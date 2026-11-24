import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
"""the saved isotropic split (4,1) spaces: independent verification (5x5 level space), invariants, and extension attempts to dim 5."""
import numpy as np, time
from core import *
from di_core import *
from di_ext import ext, chk_m, mperp
np.set_printoptions(linewidth=220, precision=3, suppress=True)
w = w3; m = np.array([1, w, w * w, 0, 0]); Y1 = np.outer(np.eye(4)[3], m)
H = np.load('r3_iso4_s0.npy'); mode = sys.argv[1]
for idx, F4 in enumerate(H):
    ed, Cb, lev, sv = defect(F4)
    if mode == 'check':
        # 5x5 space L(L') = L' (+) e_5 (x) {1,m}^perp   (bilinear perp)
        Wb = np.linalg.svd(np.array([np.ones(5), m]))[2][2:].conj()
        assert np.abs(Wb @ m).max() < 1e-12 and np.abs(Wb.sum(1)).max() < 1e-12
        L5 = [np.vstack([b, np.zeros(5)]) for b in F4] + [np.vstack([np.zeros((4, 5)), v[None]]) for v in Wb]
        S = F4.sum(-1); q = rank(S, 1e-7); L0, _ = kernel_of(F4, lambda Y: Y.sum(0)); N0, _ = kernel_of(L0, lambda Y: Y.sum(1))
        colrk = [rank(F4[:, :, j], 1e-6) for j in range(5)]; rowrk = [rank(F4[:, i, :], 1e-6) for i in range(4)]
        srow = [len(kernel_of(F4, lambda Y: np.delete(Y, i, axis=0))[0]) for i in range(4)]
        print('#%d: e=%d defect sv %s; 5x5 space: dim %d level err %.1e; q=%d, ker kappa: dim %d (q0,d0)=(%d,%d); col ranks %s row ranks %s single-row dims %s' % (
            idx, ed, np.round(sv[:3], 10), rank(np.array(L5)), level_check(np.array(L5)), q, len(L0), rank(L0.sum(-1), 1e-7), len(N0), colrk, rowrk, srow))
        m_found = Cb[0] / Cb[0][np.argmax(np.abs(Cb[0]))]; print('     defect line found:', np.round(m_found, 4))
    if mode == 'ext':
        t0 = time.time(); s5, n5 = ext(F4, m, 60, 1000 + idx, tmax=75)
        print('#%d: extensions to dim 5: %d/%d (%.0fs)' % (idx, len(s5), n5, time.time() - t0), flush=True)
        if s5: np.save('r3_iso5_%d.npy' % idx, np.concatenate([F4, s5[0][None]]))
