import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
"""(1) fourth exact (4,1) example R (+) e_i (e_0-e_1)^T with (q,Nbar,zeta) = (1,2,1); (2) calibrated extension test of Theorem TC5:
   each exact two-column (4,1) space: a random 3-dim subspace re-extends (calibration), the space itself does not (m fixed)."""
import numpy as np
from core import *
from di_core import *
from di_ext import ext, chk_m
w = w3; e = np.eye(5); rng = np.random.default_rng(3)
uh = np.array([1, w, 0, w ** 2]); ub = np.array([1, w ** 2, 0, w]); z1 = np.array([1, 1, -1, 1]) / 2; hp = np.array([1, 1, -3, 1.])
R4 = np.array([np.outer(chi(1), e[2]), np.outer(chi(1), e[3]), np.outer(chi(1), e[4]), np.outer(np.eye(4)[0], e[0] - e[1])])
ed, Cb, lev, sv = defect(R4); print('R (+) e_0(e_0-e_1)^T: dim', rank(R4), 'e =', ed, 'level err %.1e' % lev, 'm =', np.round(Cb[0] / Cb[0][0], 6) if ed else None)
q = rank(R4.sum(-1), 1e-9); Np, _ = kernel_of(R4, lambda Y: Y.sum(1)); zt, _ = kernel_of(R4, lambda Y: np.concatenate([Y[:, 2:].ravel(), Y[:, 0] + Y[:, 1]]))
print('   (q, dim Nbar, dim zeta) = (%d,%d,%d)' % (q, len(Np) - len(zt), len(zt)))
# permute columns so that every example has m = e_0 - e_1
P03 = [0, 3, 1, 2, 4]    # new column order: old columns 0,3 first
ex = {'exact7b': np.array([np.outer(uh, e[0] - e[3]), np.outer(ub, e[1]), np.outer(ub, e[4]), np.outer(hp, e[2])])[:, :, P03],
      'third kind': np.array([np.outer(uh, e[0] - e[3]), np.outer(z1, e[0] - e[3]), np.outer(ub, e[1]), np.outer(ub, e[4])])[:, :, P03],
      'R + e_0 m^T': R4}
m = e[0] - e[1]
for nm, B in ex.items():
    assert chk_m(B, m) < 1e-9
    c = rng.normal(size=(3, 4)) + 1j * rng.normal(size=(3, 4)); F = np.einsum('ki,iab->kab', c, B)
    cal, n1 = ext(F, m, 8, 5, tmax=25); tst, n2 = ext(B, m, 14, 6, tmax=40)
    print(f'{nm:12s}: calibration (random 3-dim subspace): {len(cal)}/{n1} extensions; the 4-dim space itself: {len(tst)}/{n2} extensions')
