import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""Prop II checks.  (1) t^2-coefficients of T_j(Y + tZ), Z = mu zeta (e_0-e_1)^T + mu' conj(zeta) (e_3-e_4)^T, Y column-centred (random):
       T_2: -mu^2<zb,y3+y4> - mu'^2<z,y0+y1>;  T_0: mu mu'<1_3,y3-y4> - mu'^2<z,y1+y2>;  T_1: -mu mu'<1_3,y3-y4> - mu'^2<z,y0+y2>;
       T_3: -mu^2<zb,y2+y4> + mu mu'<1_3,y0-y1>;  T_4: -mu^2<zb,y2+y3> - mu mu'<1_3,y0-y1>.
   (2) on 3-dim spaces containing the type II plane (found by climbing) the linear constraints of Prop II hold."""
import numpy as np, itertools, time
from core import *
from di_core import *
from di_ext import *
rng = np.random.default_rng(8); cn = lambda *s: rng.normal(size=s) + 1j * rng.normal(size=s); d = lambda a, b: np.sum(a * b)
w = w3; z = np.array([1, w, w * w, 0]); zb = np.array([1, w * w, w, 0]); one3 = np.array([1, 1, 1, 0.])
def T(M, j): cols = [c for c in range(5) if c != j]; return sum(np.sum(M[:, a] * M[:, b] * M[:, c]) for a, b, c in itertools.combinations(cols, 3))
worst = 0
for _ in range(20):
    Y = cn(4, 5); Y -= Y.mean(0, keepdims=True); mu, mup = cn(2)
    Z = np.zeros((4, 5), complex); Z[:, 0] = mu * z; Z[:, 1] = -mu * z; Z[:, 3] = mup * zb; Z[:, 4] = -mup * zb
    ts = np.array([0, 1, -1, 2.]); V4 = np.vander(ts, 4, increasing=True); y = [Y[:, j] for j in range(5)]
    pred = [mu * mup * d(one3, y[3] - y[4]) - mup ** 2 * d(z, y[1] + y[2]), -mu * mup * d(one3, y[3] - y[4]) - mup ** 2 * d(z, y[0] + y[2]),
            -mu ** 2 * d(zb, y[3] + y[4]) - mup ** 2 * d(z, y[0] + y[1]), -mu ** 2 * d(zb, y[2] + y[4]) + mu * mup * d(one3, y[0] - y[1]),
            -mu ** 2 * d(zb, y[2] + y[3]) - mu * mup * d(one3, y[0] - y[1])]
    for j in range(5):
        co = np.linalg.solve(V4, np.array([T(Y + t * Z, j) for t in ts])); worst = max(worst, abs(co[2] - pred[j]))
print('(1) t^2-coefficients of T_j: max error %.1e' % worst)
Z1 = np.zeros((4, 5), complex); Z1[:, 0] = z; Z1[:, 1] = -z; Z2 = np.zeros((4, 5), complex); Z2[:, 3] = zb; Z2[:, 4] = -zb
for mn, m in {'(1,2,-3,0,0)': np.array([1, 2, -3, 0, 0.]), '(1,1,-2,0,0)': np.array([1, 1, -2, 0, 0.])}.items():
    for run in range(3):
        sols, n = ext(np.array([Z1 / np.linalg.norm(Z1), Z2 / np.linalg.norm(Z2)]), m, 8, 500 + run, tmax=12)
        for E in sols[:3]:
            s = E.sum(1); y = [E[:, j] for j in range(5)]
            lin = [d(zb, y[3]), d(zb, y[4]), d(zb, y[2]), d(zb, s), d(one3, y[3] - y[4]), d(one3, y[0] - y[1]), d(z, y[0]) - d(z, s) / 2, d(z, y[1]) - d(z, s) / 2]
            extra = [d(z, y[2]) - d(z, s) * m[2] / (2 * m[0])] + ([d(z, s)] if abs(m[0] - m[1]) > 1e-9 else [])
            print('(2) m = %s: extension with |col sums| %.1e, |s| %.2f: max |linear constraints| %.1e, m-dependent ones %.1e' % (
                mn, np.abs(E.sum(0)).max(), np.linalg.norm(s), np.abs(lin).max(), np.abs(extra).max()), flush=True)
