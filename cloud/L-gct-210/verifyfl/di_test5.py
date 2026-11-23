import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""error-catching test of DI5.2/DI5.3 on every available two-column e = 1 space:
   (C2'),(C3'),(C4') in symmetrised form, Lemma Z (Z1),(Z2), Lemma NB, dim L' = q + dim Nbar + dim zeta = dim L'' + dim D, and that the
   proof's exclusions do not apply (types allowed: dim zeta = 2 => dim L'' <= 2; Nbar != 0 => q = 2 degenerate; dim Nbar <= 2; not (2,2,1))."""
import numpy as np, itertools, glob
from core import *
from di_core import *
dot = lambda a, b: np.sum(a * b)
def Efun(d): return (d.sum() ** 2 - dot(d, d)) / 2 - d * d.sum() + d * d
def pm(*cols): return perm(np.array(cols).T)
def Tb(cols): return sum(tau(cols[a] * cols[b] * cols[c]) for a, b, c in itertools.combinations(range(len(cols)), 3))
w = w3; e = np.eye(5); uh = np.array([1, w, 0, w ** 2]); ub = np.array([1, w ** 2, 0, w]); z1 = np.array([1, 1, -1, 1]) / 2; hp = np.array([1, 1, -3, 1.])
sp = {'exact7b': (np.array([np.outer(uh, e[0] - e[3]), np.outer(ub, e[1]), np.outer(ub, e[4]), np.outer(hp, e[2])]), 0, 3),
      'third kind': (np.array([np.outer(uh, e[0] - e[3]), np.outer(z1, e[0] - e[3]), np.outer(ub, e[1]), np.outer(ub, e[4])]), 0, 3),
      'M_2': (np.array([np.outer(np.array([1, w, w * w, 0]), e[0] - e[1]), np.outer(np.array([1, 1, 1, -1.]), e[0] - e[1])]), 0, 1)}
for f in sorted(glob.glob('di_gr_k*_s*.npy')):
    for i, B in enumerate(np.load(f)): sp['%s#%d' % (f[:-4], i)] = (B, 0, 1)
B6 = onb(np.load('/home/claude/work/L-gct-210/rows/seed_d4_e1_t6.npy')); ed, Cb, lev, sv = defect(B6); m6 = Cb[0]; ab = np.argsort(-np.abs(m6))[:2]
sp['rows seed t6'] = (B6, int(min(ab)), int(max(ab)))
rng = np.random.default_rng(2); bad = 0
for nm, (B, a, b) in sp.items():
    B = onb(B); ed, Cb, lev, sv = defect(B)
    if ed != 1 or lev > 1e-8: print(nm, 'skipped: e =', ed, 'level err %.1e' % lev); continue
    neu = [j for j in range(5) if j not in (a, b)]
    q = rank(B.sum(-1), 1e-7)
    Np, _ = kernel_of(B, lambda Y: Y.sum(1)); zt, _ = kernel_of(B, lambda Y: np.concatenate([Y[:, neu].ravel(), Y[:, a] + Y[:, b]]))
    Lpp, _ = kernel_of(B, lambda Y: Y[:, a] - Y[:, b]); dimD = rank(np.array([Y[:, a] - Y[:, b] for Y in B]), 1e-7)
    nbar = len(Np) - len(zt); errs = {}
    for _ in range(12):
        c = rng.normal(size=len(B)) + 1j * rng.normal(size=len(B)); Y = np.einsum('i,iab->ab', c, B)
        u = (Y[:, a] + Y[:, b]) / 2; d = (Y[:, a] - Y[:, b]) / 2; y = [Y[:, j] for j in neu]; s = Y.sum(1)
        Q = d.sum() ** 2 - dot(d, d)
        errs['C2 neutral'] = max(errs.get('C2 neutral', 0), max(abs(dot(v, v) - dot(s, v)) for v in y))
        errs['C2 u'] = max(errs.get('C2 u', 0), abs(dot(u, u) - dot(s, u) - Q))
        errs['C3 u-del'] = max(errs.get('C3 u-del', 0), abs(Tb([u] + y)))
        errs['C4 u-del'] = max(errs.get('C4 u-del', 0), abs(perm_cols(u, *y)))
        for j, (k, l) in zip(range(3), ((1, 2), (0, 2), (0, 1))):
            errs['C3 j'] = max(errs.get('C3 j', 0), abs(Tb([u, u, y[k], y[l]]) - dot(y[k] + y[l], Efun(d))))
            errs['C4 j'] = max(errs.get('C4 j', 0), abs(perm_cols(u, u, y[k], y[l]) - pm(d, d, y[k], y[l])))
        for Zz in zt:
            z = Zz[:, a]
            errs['Z1 Q(z)'] = max(errs.get('Z1 Q(z)', 0), abs(z.sum() ** 2 - dot(z, z)))
            errs['Z1 eps'] = max(errs.get('Z1 eps', 0), abs(d.sum() * z.sum() - dot(d, z)))
            errs['Z2 E(z)'] = max(errs.get('Z2 E(z)', 0), max(abs(dot(v, Efun(z))) for v in y))
            errs['Z2 perm'] = max(errs.get('Z2 perm', 0), max(abs(pm(z, z, y[k], y[l])) + abs(pm(d, z, y[k], y[l])) for k, l in ((0, 1), (0, 2), (1, 2))))
    # Nbar columns isotropic on neutral columns
    iso = max([abs(dot(Z[:, j], Z2[:, j])) for Z in Np for Z2 in Np for j in neu] + [0])
    ok_types = (len(zt) < 2 or len(Lpp) <= 2) and nbar <= 2 and not (q == 2 and nbar == 2 and len(zt) == 1) and (nbar == 0 or q <= 2)
    Gs = np.array([[dot(x, y_) for y_ in B.sum(-1)] for x in B.sum(-1)]); 
    mxe = max(errs.values()) if errs else 0
    bad += (mxe > 1e-6) or (iso > 1e-6) or (not ok_types) or (len(B) != q + nbar + len(zt)) or (len(B) != len(Lpp) + dimD)
    print(f'{nm:22s} dim {len(B)} (q,Nbar,zeta)=({q},{nbar},{len(zt)}) (L\'\',D)=({len(Lpp)},{dimD}) max identity err {mxe:.1e} Nbar isotropy {iso:.1e} allowed-type {ok_types}')
print('violations:', bad)
