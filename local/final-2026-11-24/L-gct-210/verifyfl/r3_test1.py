import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
"""Round 3: split case.  Check on every split example:  C(Y) = D(Y3)(1+rho),  D(Y3) m = mu m,
   thetahat(Y) <m,m> = mu(Y3) <m,rho(Y)>,  <m,rho(Y)> = kappa(Y) <m,m>,  hence thetahat = kappa * mu."""
import numpy as np, itertools
from core import *
from di_core import *
P3 = list(itertools.permutations(range(3)))
def perm3(M): return sum(M[0, p[0]] * M[1, p[1]] * M[2, p[2]] for p in P3)
def Dmat(Y3):
    X = 1 + Y3; D = np.zeros((5, 5), complex)
    for j in range(5):
        for k in range(5):
            if j != k: D[j, k] = perm3(X[:, [l for l in range(5) if l not in (j, k)]])
    return D
if __name__ == '__main__':
    sp = load_rows('clm_p4_d4_defect1_s*.npy'); sp.update(load_rows('seed_d4_e1_t*.npy'))
    e5 = np.eye(5); R4 = onb(np.array([np.outer(chi(1), e5[2]), np.outer(chi(1), e5[3]), np.outer(chi(1), e5[4]), np.outer(np.eye(4)[0], e5[0] - e5[1])]))
    sp['L_4 (exact)'] = R4
    rng = np.random.default_rng(1); worst = {}; n = 0
    for nm, B in sp.items():
        e, Cb, lev, sv = defect(B)
        if e != 1: continue
        m = Cb[0]; m = m / m[np.argmax(np.abs(m))]
        split = [i for i in range(4) if rank(np.concatenate([B, np.outer(np.eye(4)[i], m)[None]]).reshape(len(B) + 1, -1), 1e-6) == len(B)]
        if not split: continue
        i = split[0]; n += 1; mm = np.sum(m * m)
        for _ in range(6):
            c = rng.normal(size=len(B)) + 1j * rng.normal(size=len(B)); Y = np.einsum('k,kab->ab', c, B)
            Y3 = np.delete(Y, i, axis=0); rho = Y[i]; D = Dmat(Y3); C = Cvec(Y)
            th = np.sum((C - 24) * m.conj()) / np.sum(np.abs(m) ** 2)            # C - 24 = th m
            Dm = D @ m; mu = np.sum(Dm * m.conj()) / np.sum(np.abs(m) ** 2)
            kap = np.sum(Y.sum(0) * m.conj()) / np.sum(np.abs(m) ** 2)
            for key, val in (('C = D(1+rho)', np.abs(C - D @ (1 + rho)).max()), ('Dm = mu m', np.abs(Dm - mu * m).max()),
                             ('th<m,m> = mu<m,rho>', abs(th * mm - mu * np.sum(m * rho))), ('<m,rho> = kappa<m,m>', abs(np.sum(m * rho) - kap * mm)),
                             ('th = kappa mu', abs(th - kap * mu))):
                worst[key] = max(worst.get(key, 0), val / (1 + abs(th) + abs(mu)))
    print('split examples tested:', n)
    for k, v in worst.items(): print(f'  {k:24s} {v:.1e}')
