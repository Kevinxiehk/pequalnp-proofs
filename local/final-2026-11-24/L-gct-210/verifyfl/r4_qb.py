import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
"""Lemma QB on the e = 1 example spaces: (a) sum <y_a,y_a> = <s,s> + kappa^2 <m,m>; (b) (<b_j,b_j> - <s,s> - 3 kappa^2 m_j^2) = -2 theta_2 m_j
   (so the vector over j is proportional to m; theta_2 extracted from the degree-2 part of C - 24)."""
import numpy as np, glob
from core import *
from di_core import *
dot = lambda a, b: np.sum(a * b)
sp = load_rows('clm_p4_d4_defect1_s*.npy'); sp.update(load_rows('seed_d4_e1_t*.npy'))
for f_ in ['r3_z3_good.npy', 'r3_iso4_s0.npy']:
    for i, B in enumerate(np.load(f_)): sp['%s#%d' % (f_, i)] = B
rng = np.random.default_rng(3); wa = wb = 0; n = 0
for nm, B in sp.items():
    B = onb(B); e, Cb, lev, sv = defect(B)
    if e != 1 or lev > 1e-8: continue
    m = Cb[0]; m = m / m[np.argmax(np.abs(m))]; n += 1
    for _ in range(5):
        c = rng.normal(size=len(B)) + 1j * rng.normal(size=len(B)); Y = np.einsum('k,kab->ab', c, B)
        kap = dot(Y.sum(0), m) / dot(m, m) if abs(dot(m, m)) > 1e-6 else (Y.sum(0)[np.argmax(np.abs(m))] / m[np.argmax(np.abs(m))])
        s = Y.sum(1); wa = max(wa, abs(sum(dot(Y[:, j], Y[:, j]) for j in range(5)) - dot(s, s) - kap ** 2 * dot(m, m)) / (1 + abs(dot(s, s))))
        # degree-2 part of C - 24 by finite scaling: C(tY) = 24 + t c1 + t^2 c2 + t^3 c3 + t^4 c4
        ts = np.array([1, -1, 2, -2, 0.5]); Cs = np.array([Cvec(t * Y) - 24 for t in ts]); co = np.linalg.lstsq(np.vander(ts, 5, increasing=True)[:, 1:], Cs, rcond=None)[0]
        th2 = co[1] @ m.conj() / (m @ m.conj())
        lhs = np.array([dot(2 * (Y[:, j] - kap * m[j] / 4) - s, 2 * (Y[:, j] - kap * m[j] / 4) - s) - dot(s, s) - 3 * kap ** 2 * m[j] ** 2 for j in range(5)])
        wb = max(wb, np.abs(lhs + 2 * th2 * m).max() / (1 + np.abs(lhs).max()))
print('Lemma QB on %d spaces with e = 1: (a) %.1e, (b) %.1e' % (n, wa, wb))
