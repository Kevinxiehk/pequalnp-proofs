import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
"""Round 4 checks.
 (1) principal-stratum normal form on the split (4,1) examples: H = ker kappa strongly level with s(H) = V, isometries B_j,
     Z = e_i m^T = sum m_j h_j e_j^T, h_j = 1/4 - 2 B_j f, <f,f> = 3/16, f defined by Lemma B' polarisation.
 (2) column-centred spaces with defect line C m: E_3 := tau(e_3(Y)) = 0 and X_j := tau((b_j+s)(2b_j^2+3s^2-sum b_k^2)) in C m_j."""
import numpy as np, itertools, glob
from core import *
from di_core import *
dot = lambda a, b: np.sum(a * b)
sp = load_rows('clm_p4_d4_defect1_s*.npy')
for f_ in sorted(glob.glob('r3_gr2_*.npy')) + ['r3_gr_A_k4.npy']:
    try:
        for i, B in enumerate(np.load(f_)): sp['%s#%d' % (f_[:-4], i)] = onb(B)
    except Exception as ex: pass
worst = {}; n = 0
def rec(k, v): worst[k] = max(worst.get(k, 0), abs(v))
for nm, B in sp.items():
    e, Cb, lev, sv = defect(B)
    if e != 1 or lev > 1e-9: continue
    m = Cb[0]; m = m / m[np.argmax(np.abs(m))]
    split = [i for i in range(4) if rank(np.concatenate([B, np.outer(np.eye(4)[i], m)[None]]).reshape(len(B) + 1, -1), 1e-6) == len(B)]
    H, _ = kernel_of(B, lambda Y: Y.sum(0))
    if not split or len(H) != 3 or sl_check(H, trials=20) > 1e-7 or rank(H.sum(-1), 1e-7) != 3: continue
    i = split[0]; n += 1; P = [j for j in range(5) if abs(m[j]) > 1e-6]
    S = H.sum(-1)                                   # (3,4): s(H_k)
    coords = lambda sig: np.linalg.lstsq(S.T, sig, rcond=None)[0]
    # B_j as maps V -> V: b_j(Y) = 2 y_j - s  on H
    Vb = np.linalg.svd(np.ones((1, 4)))[2][1:].conj()          # orthonormal real basis of V (3,4)
    Bj = []
    for j in range(5):
        Mj = np.array([2 * np.einsum('k,ka->a', coords(v), H[:, :, j]) - v for v in Vb])     # rows: B_j v
        Bj.append(Mj)
        rec('B_j isometry', np.abs(Mj @ Mj.T - np.eye(3)).max())
    Z = np.outer(np.eye(4)[i], m)
    # theta_2' polar between H and Z from Lemma B': <b_j(Y0), b_j(Z)> = -4 m_j Theta'(Y0,Z)  -> <B_j sigma, 2 z_j^0> = -4 m_j <f, sigma>
    j0 = P[0]; z0 = Z[:, j0] - Z[:, j0].mean()
    fvec = np.array([dot(Bj[j0][k], 2 * z0) / (-4 * m[j0]) for k in range(3)]) @ Vb          # f in V with <f, v_k> = ...
    rec('<f,f> - 3/16', dot(fvec, fvec) - 3 / 16)
    for j in P:
        # B_j f  (apply the map: f = sum c_k Vb_k -> sum c_k Bj[k])
        ck = Vb @ fvec; Bf = ck @ Bj[j]
        rec('h_j = 1/4 - 2 B_j f = e_i', np.abs(0.25 - 2 * Bf - np.eye(4)[i]).max())
print('(1) principal split (4,1) examples tested: %d' % n)
for k, v in worst.items(): print('    %-34s %.1e' % (k, v))
# (2)
try:
    G = np.load('r3_z3_good.npy'); m = np.array([1, 2, -3, 0, 0.]); rng = np.random.default_rng(0); w2 = {}
    for B in G:
        for _ in range(8):
            c = rng.normal(size=len(B)) + 1j * rng.normal(size=len(B)); Y = np.einsum('k,kab->ab', c, B)
            s = Y.sum(1); b = [2 * Y[:, j] - s for j in range(5)]; sb2 = sum(x * x for x in b)
            E3 = sum(tau(Y[:, a] * Y[:, bb] * Y[:, cc]) for a, bb, cc in itertools.combinations(range(5), 3))
            X = np.array([tau((b[j] + s) * (2 * b[j] ** 2 + 3 * s * s - sb2)) for j in range(5)])
            Tj = np.array([Pk(dele(Y, j))[2] / 2 for j in range(5)])
            w2['E_3 = 0'] = max(w2.get('E_3 = 0', 0), abs(E3)); w2['T_j = E_3 - X_j/16'] = max(w2.get('T_j = E_3 - X_j/16', 0), np.abs(Tj - (E3 - X / 16)).max())
            th = dot(X, m) / dot(m, m); w2['X_j in C m_j'] = max(w2.get('X_j in C m_j', 0), np.abs(X - th * m).max())
    print('(2) column-centred genuine (3,1) spaces, m = (1,2,-3,0,0): %d spaces' % len(G))
    for k, v in w2.items(): print('    %-34s %.1e' % (k, v))
except Exception as ex: print('(2) skipped', ex)
