import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
"""Theorem PR3 checks.  (1) formula on the family  Y = kappa h0 m^T + chi_1 lam^T  (m supported on P = {0,1,2}):
       C_a - 24 = -6 kappa m_a (a in P),  C_n - 24 = 2 kappa (4 beta Q_m(lam) - (3/8) e_3(m) kappa^2)  (n neutral).
   (2) isotropic m = (1,w,w^2,0,0): the plane N = {l(lam) = xi kappa} is a 2-dim level space with defect in C m.
   (3) greedy climb from N with m fixed (argv: seed tmax)."""
import numpy as np, time
from core import *
from di_core import *
from di_ext import *
rng = np.random.default_rng(1); cn = lambda *s: rng.normal(size=s) + 1j * rng.normal(size=s)
chi1 = chi(1); chi2 = chi(2); w = w3
def fam(m, beta, kap, lam):
    h0 = 0.25 + beta * chi2; Y = np.zeros((4, 5), complex); Y[:, :3] = kap * np.outer(h0, m[:3]) + np.outer(chi1, lam); return Y
worst = 0
for trial in range(40):
    m = np.zeros(5, complex); m[:2] = cn(2); m[2] = -m[0] - m[1]; beta = (1 if trial % 2 else -1) * np.sqrt(3) / 4
    lam = cn(3); lam[2] = -lam[0] - lam[1]; kap = cn(1)[0]
    Y = fam(m, beta, kap, lam); C = Cvec(Y) - 24
    Q = m[0] * lam[1] * lam[2] + m[1] * lam[0] * lam[2] + m[2] * lam[0] * lam[1]; e3 = m[0] * m[1] * m[2]
    pred = np.concatenate([-6 * kap * m[:3], [2 * kap * (4 * beta * Q - 0.375 * e3 * kap ** 2)] * 2])
    worst = max(worst, np.abs(C - pred).max())
print('(1) formula for C(Y) on the family: max error %.1e' % worst)
m = np.array([1, w, w * w, 0, 0]); mbar = np.array([1, w * w, w, 0, 0])
def Nplane(beta, sgn):
    xi = sgn * np.sqrt(complex(-3 / (32 * beta)))            # l(lam)^2 = -3 kappa^2/(32 beta),  l(lam) = lam_b - w^2 lam_a,  Q_m = -l^2
    lam = np.array([0, xi, -xi]); Z = fam(m, beta, 1, lam); Zs = np.zeros((4, 5), complex); Zs[:, :3] = np.outer(chi1, mbar[:3])
    return np.array([Z, Zs])
if __name__ == '__main__':
    seed = int(sys.argv[1]); tmax = float(sys.argv[2]); t0 = time.time()
    for beta in (np.sqrt(3) / 4, -np.sqrt(3) / 4):
        for sgn in (1, -1):
            N = Nplane(beta, sgn); e, Cb, lev, sv = defect(N)
            print('(2) beta %+.3f sign %+d: N dim %d, defect dim %d, level err %.1e, defect-in-Cm residual %.1e' % (beta, sgn, rank(N.reshape(2, -1), 1e-9), e, lev, chk_m(N, m)), flush=True)
    for run in range(6):
        if time.time() - t0 > tmax: break
        beta = (np.sqrt(3) / 4) * (1 if run % 2 == 0 else -1); sgn = 1 if (run // 2) % 2 == 0 else -1
        F = list(Nplane(beta, sgn)); dims = [2]
        while len(F) < 5 and time.time() - t0 < tmax:
            sols, n = ext(np.array(F), m, 10, seed + 100 * run + len(F), tmax=min(22, max(3, tmax - (time.time() - t0))))
            if not sols: break
            F.append(sols[(seed + run) % len(sols)]); dims.append(len(F))
        B = onb(np.array(F)); H, _ = kernel_of(B, lambda Y: Y.sum(0))
        split = [i for i in range(4) if rank(np.concatenate([B, np.outer(np.eye(4)[i], m)[None]]).reshape(len(B) + 1, -1), 1e-6) == len(B)]
        print('(3) run %d (beta %+.2f, sign %+d): reached dim %d, residual %.1e, ker kappa dim %d (sl err %.1e, rank s = %d), split rows %s' % (
            run, beta, sgn, len(F), chk_m(B, m), len(H), sl_check(H, trials=20) if len(H) else 0, rank(H.sum(-1), 1e-7) if len(H) else 0, split), flush=True)
        np.save('r4_pr3_climb_%d_%d.npy' % (seed, run), B)
