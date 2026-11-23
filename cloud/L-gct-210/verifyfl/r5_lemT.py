import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""Round 5 identity checks (random points).
 (a) bracket pairing:  [z_a,z_b,z_c,u] = <-6 z_a z_b z_c + th sum m_j z_j, u>  when <z_j,z_k> = th m_l  (here just the general formula);
 (b) [chi_1,chi_1,u,u'] = -6<chi_2,uu'> + 2<chi_1,u><chi_1,u'>, and = 8 rho rho' for u = k chi_2 + rho chi_3, u' = k' chi_2 + rho' chi_3;
 (c) t-expansion: for Y column-centred and Z = chi_1 l^T (l on columns 0,1,2, sum 0):
       t^3-coefficient of [Y+tZ]^(delete col 4)  = -6 l_a l_b l_c <chi_3, y_3>,
       t^2-coefficient of T_0(Y+tZ) = l_b l_c <chi_2, y_3 + y_4>,
       t^2-coefficient of bracket(delete col 0) = l_b l_c [chi_1,chi_1,y_3,y_4]."""
import numpy as np, itertools
from core import *
rng = np.random.default_rng(5); cn = lambda *s: rng.normal(size=s) + 1j * rng.normal(size=s); d = lambda a, b: np.sum(a * b)
def br(a, b, c, e): return -6 * np.sum(a * b * c * e) + d(a, b) * d(c, e) + d(a, c) * d(b, e) + d(a, e) * d(b, c)
def cen(x): return x - x.mean(0, keepdims=True)
c1, c2, c3 = chi(1), chi(2), chi(3); wa = wb = wc = 0
for _ in range(20):
    u, up = cen(cn(4)), cen(cn(4))
    wb = max(wb, abs(br(c1, c1, u, up) - (-6 * d(c2, u * up) + 2 * d(c1, u) * d(c1, up))))
    k, r, kp, rp = cn(4); wb = max(wb, abs(br(c1, c1, k * c2 + r * c3, kp * c2 + rp * c3) - 8 * r * rp))
    Y = cen(cn(4, 5)); l = cn(3); l[2] = -l[0] - l[1]; Z = np.zeros((4, 5), complex); Z[:, :3] = np.outer(c1, l)
    def T(M, j): cols = [c for c in range(5) if c != j]; return sum(np.sum(M[:, a] * M[:, b] * M[:, c]) for a, b, c in itertools.combinations(cols, 3))
    def B(M, j): cols = [c for c in range(5) if c != j]; return br(*[M[:, c] for c in cols])
    ts = np.array([0, 1, -1, 2, -2.]); V5 = np.vander(ts, 5, increasing=True)
    co = np.linalg.solve(V5, np.array([B(Y + t * Z, 4) for t in ts])); wc = max(wc, abs(co[3] - (-6 * l[0] * l[1] * l[2] * d(c3, Y[:, 3]))))
    co = np.linalg.solve(V5, np.array([T(Y + t * Z, 0) for t in ts])); wc = max(wc, abs(co[2] - l[1] * l[2] * d(c2, Y[:, 3] + Y[:, 4])))
    co = np.linalg.solve(V5, np.array([B(Y + t * Z, 0) for t in ts])); wc = max(wc, abs(co[2] - l[1] * l[2] * br(c1, c1, Y[:, 3], Y[:, 4])))
    co = np.linalg.solve(V5, np.array([T(Y + t * Z, 3) for t in ts]))       # delete neutral column 3: columns 0,1,2,4
    pred = l[0] * l[1] * d(c2, Y[:, 2]) + l[0] * l[2] * d(c2, Y[:, 1]) + l[1] * l[2] * d(c2, Y[:, 0]) + (l[0] * l[1] + l[0] * l[2] + l[1] * l[2]) * d(c2, Y[:, 4])
    wc = max(wc, abs(co[2] - pred))
print('(b) bracket [chi_1,chi_1,u,u\'] formulas: %.1e;  (c) t-coefficients (alpha), (beta), (delta), (c2-n): %.1e' % (wb, wc))
