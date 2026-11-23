import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""TASK 2b: step-specific checks of the case analysis (types I-IV, g = 1, g = 2)."""
import numpy as np, itertools
from core import *
rng = np.random.default_rng(3)
cn = lambda *s: rng.normal(size=s) + 1j * rng.normal(size=s)
dot = lambda a, b: tau(a * b)
v = lambda t: chi(1) + t * chi(2) - t * t / 2 * chi(3)
P3d = lambda Y, m: Pk(dele(Y, m))[2]
P4d = lambda Y, m: perm(dele(Y, m))
e = np.eye(5)
print('--- g = 1: v (x) Lambda')
# (a) C3_m = 2 tau(v^3) (e3 - l_m e2 - l_m^3) for sum l = 0 ; C4_m = -6 tau(v^4) prod_{a != m} l_a
for _ in range(5):
    t = cn(1)[0]; x = v(t); l = cn(5); l -= l.mean(); Y = np.outer(x, l)
    e2 = sum(l[a] * l[b] for a, b in itertools.combinations(range(5), 2)); e3 = sum(l[a] * l[b] * l[c] for a, b, c in itertools.combinations(range(5), 3))
    err = max(abs(P3d(Y, m) - 2 * tau(x ** 3) * (e3 - l[m] * e2 - l[m] ** 3)) for m in range(5))
    err4 = max(abs(P4d(Y, m) + 6 * tau(x ** 4) * np.prod(np.delete(l, m))) for m in range(5))
    print('   C3 err %.1e  C4 err %.1e' % (err, err4))
zeta = np.array([1, w3, w3 ** 2, 0]); zb = zeta.conj()
print('   zero-entry isotropic zeta: tau(z^2)=%.1e tau(z^3)=%s tau(z^4)=%.1e ; chi_1: tau^3 = %.1e, tau^4 = %s' % (abs(dot(zeta, zeta)), np.round(tau(zeta ** 3), 12), abs(tau(zeta ** 4)), abs(tau(chi(1) ** 3)), tau(chi(1) ** 4)))
print('--- type II: all solutions of tau(v v\'^2) = tau(v^2 v\') = 0 on the conic (Newton from random starts)')
def F(z):
    t, u = z
    return np.array([2 * u + t + t * u ** 4 / 4 + t * t * u ** 3 / 2, 2 * t + u + u * t ** 4 / 4 + u * u * t ** 3 / 2])
def Jac(z):
    t, u = z
    return np.array([[1 + u ** 4 / 4 + t * u ** 3, 2 + t * u ** 3 + 1.5 * t * t * u * u], [2 + u * t ** 3 + 1.5 * u * u * t * t, 1 + t ** 4 / 4 + u * t ** 3]])
sols = []
for _ in range(4000):
    z = cn(2) * 2
    for it in range(60):
        try: z = z - np.linalg.solve(Jac(z), F(z))
        except np.linalg.LinAlgError: break
        if not np.all(np.isfinite(z)) or abs(z).max() > 1e6: break
    else:
        if np.abs(F(z)).max() < 1e-11 and not any(np.abs(z - s).max() < 1e-6 for s in sols): sols.append(z)
diag = [s for s in sols if abs(s[0] - s[1]) < 1e-6]; off = [s for s in sols if abs(s[0] - s[1]) >= 1e-6]
print('   affine solutions found: %d (diagonal t=u: %d, off-diagonal: %d)' % (len(sols), len(diag), len(off)))
good = 0
for s in off:
    t, u = s; pm = perm_cols(v(t), v(t), v(u), v(u)); x, z = v(t), v(u)
    zr = [k for k in range(4) if abs(x[k]) < 1e-8 and abs(z[k]) < 1e-8]
    print('   t=%s u=%s a=%s b=%s perm=%s common zero rows %s' % (np.round(t, 4), np.round(u, 4), np.round(t + u, 4), np.round(t * u, 4), np.round(pm, 6), zr))
    good += (abs(pm) < 1e-8)
    assert (abs(pm) < 1e-8) == (len(zr) == 1)
print('   off-diagonal solutions with perm = 0: %d (expected 8 = 4 rows x 2 orders), all have a common zero row' % good)
print('   point at infinity v\' = chi_3: tau(v(t) chi_3^2) = 4t so t = 0, perm[chi1,chi1,chi3,chi3] =', perm_cols(chi(1), chi(1), chi(3), chi(3)))
# ex1 plane is strongly level; zeta^2 = conj zeta
N2 = np.array([np.outer(zeta, e[0] - e[1]), np.outer(zb, e[2] - e[3])])
print('   ex1 plane strong-level err %.1e ; |zeta^2 - conj zeta| = %.1e' % (sl_check(N2), np.abs(zeta ** 2 - zb).max()))
print('--- type II exclusion: coefficient of t mu\'^2 in P_3(Y^(e)) equals -2 tau(u v\'^2) (and t mu^2: -2 tau(u v^2))')
for _ in range(4):
    th = cn(1)[0]; u = v(th)                                  # isotropic row-sum direction
    be = cn(4); bE = -3 * u - (be[0] + be[1]) * zeta - (be[2] + be[3]) * zb
    b = [be[0] * zeta, be[1] * zeta, be[2] * zb, be[3] * zb, bE]
    Yu = np.array([(bm + u) / 2 for bm in b]).T
    assert np.abs(Yu.sum(1) - u).max() < 1e-12
    f = lambda t, mu, mup: P3d(t * Yu + mu * N2[0] + mup * N2[1], 4)
    c1 = (f(1, 0, 1) + f(1, 0, -1)) / 2 - f(1, 0, 0); c2 = (f(1, 1, 0) + f(1, -1, 0)) / 2 - f(1, 0, 0)
    print('   coeff t mu\'^2: %s vs -2<u,zeta> = %s ; coeff t mu^2: %s vs -2<u,conj zeta> = %s' % (np.round(c1, 10), np.round(-2 * dot(u, zeta), 10), np.round(c2, 10), np.round(-2 * dot(u, zb), 10)))
print('   u perp zeta, conj zeta, 1  =>  u in C(1,1,1,-3), <u,u> = 12 c^2 != 0')
print('--- type III / g=2 (2,3): closed forms for Z = mu v(e_a-e_b)^T + v\' nu^T')
for _ in range(4):
    t, u2 = cn(2); x, z = v(t), v(u2); mu = cn(1)[0]; nu = cn(3); nu -= nu.mean()
    Z = mu * np.outer(x, e[0] - e[1]) + np.outer(z, np.concatenate([[0, 0], nu]))
    e2n = nu[0] * nu[1] + nu[0] * nu[2] + nu[1] * nu[2]; e3n = np.prod(nu)
    errs = [abs(P3d(Z, 0) - 2 * (-mu * tau(x * z * z) * e2n + tau(z ** 3) * e3n)), abs(P3d(Z, 1) - 2 * (mu * tau(x * z * z) * e2n + tau(z ** 3) * e3n)),
            abs(P3d(Z, 2) - 2 * mu ** 2 * nu[0] * tau(x * x * z)), abs(P4d(Z, 0) - 6 * mu * e3n * tau(x * z ** 3)),
            abs(P4d(Z, 2) + mu ** 2 * nu[1] * nu[2] * perm_cols(x, x, z, z))]
    print('   errs', ' '.join('%.1e' % q for q in errs))
print('--- type I exclusion')
M = [0, 1, 2]
for _ in range(3):
    # coefficient claims: t x x coefficients of P3 deletions
    th = cn(1)[0]; u = v(th); be = cn(3); b4 = v(cn(1)[0]) * cn(1)[0]; b5 = -3 * u - be.sum() * chi(1) - b4
    b = [be[0] * chi(1), be[1] * chi(1), be[2] * chi(1), b4, b5]; Yu = np.array([(bm + u) / 2 for bm in b]).T
    x = cn(3); x -= x.mean(); X = np.outer(chi(1), np.concatenate([x, [0, 0]]))
    e2x = x[0] * x[1] + x[0] * x[2] + x[1] * x[2]
    def coef(m):
        f = lambda t, k: P3d(t * Yu + k * X, m)
        return (f(1, 1) + f(1, -1)) / 2 - f(1, 0)
    print('   P3 txx coeffs: del 4: %.1e, del 5: %.1e, del 1: %.1e (errors vs closed forms)' % (
        abs(coef(3) - e2x * (2 * dot(chi(2), u) + dot(chi(2), b5))), abs(coef(4) - e2x * (2 * dot(chi(2), u) + dot(chi(2), b4))),
        abs(coef(0) - x[1] * x[2] * (dot(chi(2), b4 + b5) + 2 * dot(chi(2), u)))))
for _ in range(3):
    # u = c chi_3 : C4 deletion 5 closed form with b_4 = pi4 chi1 + rho4 chi3 (general), p_m = t beta_m/2 + x_m, r_m = t c/2
    c, t, pi4, rho4 = cn(4); be = cn(3); x = cn(3); x -= x.mean()
    ycols = [(t * be[m] / 2 + x[m]) * chi(1) + t * c / 2 * chi(3) for m in range(3)] + [t / 2 * (pi4 * chi(1) + (rho4 + c) * chi(3)), cn(4)]
    Y = np.array(ycols).T; p = np.array([t * be[m] / 2 + x[m] for m in range(3)]); e2p = p[0] * p[1] + p[0] * p[2] + p[1] * p[2]
    full = -24 * (np.prod(p) * t / 2 * pi4 + (t * c / 2) ** 3 * t / 2 * (rho4 + c)) + 8 * (e2p * (t * c / 2) * t / 2 * (rho4 + c) + p.sum() * (t / 2 * pi4) * (t * c / 2) ** 2)
    Y0 = Y.copy(); Y0[:, 3] = t / 2 * (rho4 + c) * chi(3)
    print('   u=c chi3: C4_5 general err %.1e ; with pi4 = 0: err %.1e' % (abs(P4d(Y, 4) - full), abs(P4d(Y0, 4) - t * t * c * (rho4 + c) * (2 * e2p - 1.5 * t * t * c * c))))
for _ in range(3):
    # u = c chi_1: fourth vector forms
    t, pi4, pi5 = cn(3); x = cn(3)
    Ya = np.array([x[0] * chi(1) + t * chi(2), x[1] * chi(1), x[2] * chi(1), t * pi4 * chi(1), t * pi5 * chi(1)]).T
    Yb = np.array([x[0] * chi(1), x[1] * chi(1), x[2] * chi(1), t * (chi(2) + pi4 * chi(1)), t * pi5 * chi(1)]).T
    print('   (alpha) P3 del 4: err %.1e ; (beta) P3 del 5: err %.1e' % (abs(P3d(Ya, 3) - 8 * t * (x[1] * x[2] + t * pi5 * (x[1] + x[2]))),
          abs(P3d(Yb, 4) - 8 * t * (x[0] * x[1] + x[0] * x[2] + x[1] * x[2]))))
R3p = np.array([np.outer(chi(1), e[c]) for c in range(3)]); print('   chi_1 (x) C^M strong-level err %.1e' % sl_check(R3p))
print('--- type IV (2,1,1,1): mu^2 coefficient of C3_c')
for _ in range(3):
    th = cn(4); Vm = np.array([v(th[0]), v(th[0]), v(th[1]), v(th[2]), v(th[3])]).T
    u_, s_, vh = np.linalg.svd(Vm[:, 1:]); n = np.concatenate([[0], vh[3:].conj().T[:, 0]])   # relation among 4 distinct lines
    d0 = np.array([1, -1, 0, 0, 0.])
    for m in (2, 3, 4):
        f = lambda mu, k: P3d(Vm * (mu * d0 + k * n)[None, :], m)
        cf = (f(1, 1) + f(-1, 1)) / 2 - f(0, 1)          # mu^2 kappa coefficient
        tm = th[m - 1]   # raw P_3 coefficient = normalised part n_m f(th_m) PLUS the tau(P3)/3 part n_b * 3 th_1 (4 + th_1^4)
        pred = 2 * (n[1] * 3 * th[0] * (4 + th[0] ** 4) + n[m] * (2 * th[0] ** 3 * tm ** 2 + (4 + th[0] ** 4) * tm + 8 * th[0]))
        print('   m=%d coefficient err %.1e' % (m, abs(cf - pred)), end='')
    print()
