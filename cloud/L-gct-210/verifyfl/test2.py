import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""TASK 2a: every identity used in the proof, at random complex points (target 1e-12 relative)."""
import numpy as np, itertools
from core import *
rng = np.random.default_rng(11)
cn = lambda *s: rng.normal(size=s) + 1j * rng.normal(size=s)
def V4(*s):
    x = cn(*s, 4); return x - x.mean(-1, keepdims=True)
dot = lambda a, b: tau(a * b)
mx = {}
def rec(name, err, scale=1.0):
    mx[name] = max(mx.get(name, 0), abs(err) / max(1, abs(scale)))
for _ in range(40):
    Y = V4(5).T                    # 4x5, columns y_m in V_4 (column sums zero)
    y = [Y[:, m] for m in range(5)]; s = Y.sum(1)
    Q = sum(dot(a, a) for a in y)
    w = [a - s / 2 for a in y]; W2 = sum(a * a for a in w); P2h = sum(a * a for a in y); P3h = sum(a ** 3 for a in y)
    e3 = (s ** 3 - 3 * s * P2h + 2 * P3h) / 6
    for m in range(5):
        Z = dele(Y, m); pk = Pk(Z); oth = [a for a in range(5) if a != m]
        rec('I2.P1', pk[0])
        c2 = -sum(dot(y[a], y[b]) for a, b in itertools.combinations(oth, 2)); rec('I2.P2', pk[1] - c2, pk[1])
        c3 = 2 * sum(tau(y[a] * y[b] * y[c]) for a, b, c in itertools.combinations(oth, 3)); rec('I2.P3', pk[2] - c3, pk[2])
        c4 = perm_cols(*[y[a] for a in oth]); rec('I2.P4', pk[3] - c4, pk[3]); rec('I2.P4=perm', pk[3] - perm(Z), pk[3])
        qm = dot(y[m], y[m]) - dot(s, y[m]); rec('I3', 2 * pk[1] - (Q - dot(s, s)) + 2 * qm, pk[1])
        rec('I3w', qm - (dot(w[m], w[m]) - dot(s, s) / 4), qm)
        # general C3 in w-form: P3(Y^(m))/2 = tau(e3) - (1/2) tau((w_m + s/2)(2 w_m^2 + (3/4)s^2 - W2))
        ex = tau((w[m] + s / 2) * (2 * w[m] ** 2 + 0.75 * s ** 2 - W2)); rec('I4w', pk[2] / 2 - (tau(e3) - ex / 2), pk[2])
    rec('I3sum', sum(dot(y[m], y[m]) - dot(s, y[m]) for m in range(5)) - (Q - dot(s, s)), Q)
    # DC case (s = 0): I4
    Y0 = Y.copy(); Y0[:, 4] -= s; y0 = [Y0[:, m] for m in range(5)]
    P2 = sum(a * a for a in y0); P3 = sum(a ** 3 for a in y0)
    for m in range(5):
        pk = Pk(dele(Y0, m)); rec('I4', pk[2] / 2 - (tau(P3) / 3 + tau(y0[m] * P2) / 2 - tau(y0[m] ** 3)), pk[2])
# characters and the conic
for a in range(8):
    for b in range(8): rec('chi', dot(chi(a), chi(b)) - 4 * ((a + b) % 4 == 0))
v = lambda t: chi(1) + t * chi(2) - t * t / 2 * chi(3)
for _ in range(40):
    t, u = cn(2); t4 = cn(4)
    rec('I5.iso', dot(v(t), v(t))); rec('I5.sumzero', tau(v(t)))
    rec('I5.dot', dot(v(t), v(u)) + 2 * (t - u) ** 2)
    rec('I5.sq', np.abs(v(t) ** 2 - (-t ** 3 * chi(1) + (1 + t ** 4 / 4) * chi(2) + 2 * t * chi(3))).max())
    rec('I5.cube', tau(v(t) ** 3) - 3 * t * (4 + t ** 4), t ** 5)
    rec('I5.mixed', tau(v(t) * v(u) ** 2) - 4 * (2 * u + t + t * u ** 4 / 4 + t * t * u ** 3 / 2), (abs(t) + abs(u)) ** 5)
    a, b = t + u, t * u
    pm = perm_cols(v(t), v(t), v(u), v(u)); rec('I5.perm2', pm - (2 * (a * a + 2 * b) ** 2 - 1.5 * (b * b - 4) ** 2), pm)
    e2 = sum(t4[i] * t4[j] for i, j in itertools.combinations(range(4), 2)); e4 = np.prod(t4)
    pm = perm_cols(*[v(x) for x in t4]); rec('I5.perm4(zeros formula)', pm - (2 * e2 ** 2 - 1.5 * (e4 - 4) ** 2), pm)
    # E1 +- E2 factorisations
    E1 = 2 * u + t + t * u ** 4 / 4 + t * t * u ** 3 / 2; E2 = 2 * t + u + u * t ** 4 / 4 + u * u * t ** 3 / 2
    rec('I5.sum', E1 + E2 - a / 4 * (12 + a * a * b - b * b), E1); rec('I5.diff', E1 - E2 - (u - t) / 4 * (4 + a * a * b + b * b), E1)
    # zero entry of v(t) in row k
    for k in range(4):
        rec('I5.zero', v(t)[k] - 1j ** k * (-0.5) * 1j ** (2 * k) * (t * t - 2 * 1j ** (-k) * t - 2 * 1j ** (-2 * k)), 1 + abs(t) ** 2)
    # isotropic => p4 = -4 e4 ; perm[v,v,v,v] = -6 p4 ; perm[v,v',v',v'] = -6 tau(v v'^3)
    x = v(t); rec('iso.p4', tau(x ** 4) + 4 * np.prod(x), tau(x ** 4)); rec('iso.perm1', perm_cols(x, x, x, x) + 6 * tau(x ** 4), tau(x ** 4))
    z = v(u); rec('iso.perm31', perm_cols(x, z, z, z) + 6 * tau(x * z ** 3), tau(x * z ** 3))
    rec('iso.perm22', perm_cols(x, x, z, z) - (-6 * tau(x * x * z * z) + 2 * dot(x, z) ** 2), dot(x, z) ** 2)
    # span(chi1, chi3) permanent
    p, r = cn(4), cn(4); ys = [p[i] * chi(1) + r[i] * chi(3) for i in range(4)]
    cl = -24 * (np.prod(p) + np.prod(r)) + 8 * sum(p[i] * p[j] * np.prod([r[k] for k in range(4) if k not in (i, j)]) for i, j in itertools.combinations(range(4), 2))
    rec('I6', perm_cols(*ys) - cl, cl)
rec('I7', perm_cols(chi(3), chi(3), chi(1), chi(1)) - 8)
# type IV identity: C3_m on N, lines v(theta_a), y_a = l_a v(theta_a) with sum l_a v_a = 0
for _ in range(20):
    th = cn(5); Vm = np.array([v(x) for x in th]).T      # 4x5
    u_, s_, vh = np.linalg.svd(Vm); ker = vh[3:].conj().T   # 5x2 kernel
    l = ker @ cn(2); Y = Vm * l[None, :]
    rec('IV.dc', np.abs(Y.sum(1)).max())
    A = sum(l ** 2 * (1 + th ** 4 / 4)); B = sum(l ** 2 * th); C = sum(l ** 2 * th ** 3)
    Psi = sum(l[a] ** 2 * v(th[a]) ** 2 for a in range(5)); rec('IV.Psi', np.abs(Psi - (A * chi(2) + 2 * B * chi(3) - C * chi(1))).max())
    for m in range(5):
        pk = Pk(dele(Y, m))
        G = 4 * B + 2 * th[m] * A + th[m] ** 2 * C
        # P3(Y^(m))/2 = tau(P3)/3 + l_m G - l_m^3 * 3 th(4+th^4)
        P3 = sum((l[a] * v(th[a])) ** 3 for a in range(5))
        rec('IV.C3', pk[2] / 2 - (tau(P3) / 3 + l[m] * G - l[m] ** 3 * 3 * th[m] * (4 + th[m] ** 4)), pk[2])
    # kernel parametrisation l_m = g(theta_m)/omega'(theta_m)
    om = np.array([np.prod([th[m] - th[a] for a in range(5) if a != m]) for m in range(5)])
    al, be = cn(2); l2 = (al + be * th) / om; rec('IV.ker', np.abs(Vm @ l2).max())
# type IV numbers: roots of x^5+4x
th = np.array([0] + [np.sqrt(2) * np.exp(1j * np.pi * (2 * k + 1) / 4) for k in range(4)])
rec('IV.roots', np.abs(th ** 5 + 4 * th).max()); om = 5 * th ** 4 + 4
print('omega\' at roots of x^5+4x:', np.round(om, 10), '  2*sum th^4/om^2 =', np.round(2 * np.sum(th ** 4 / om ** 2), 12))
for k, e in mx.items(): print(f'{k:28s} {e:.1e}')
print('MAX', max(mx.values()))
