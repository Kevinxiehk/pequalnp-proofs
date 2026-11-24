import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
"""Round 5 exact objects.  (v1) type V plane chi_1 (x) c^+ (+) chi_3 (x) c^- for good 3-support m;  (v2) isotropic m: U_2 (x) mbar;
   (v3) 3-column identity: with y_a = m_c Y'_b + m_b Y'_c etc.:  u_a<y_b,y_c> + u_b<y_a,y_c> + u_c<y_a,y_b> = e_3 sum_j (u_j/m_j) <Y'_j,Y'_j> for u perp m."""
import numpy as np
from core import *
from di_core import *
from di_ext import chk_m
rng = np.random.default_rng(2); cn = lambda *s: rng.normal(size=s) + 1j * rng.normal(size=s); w = w3
def cpm(m3):
    ma, mb, mc = m3            # Q_m on W_P in coordinates (c_a, c_b), c_c = -c_a - c_b:  -m_b c_a^2 - m_a c_b^2 - 2(m_a+m_b) c_a c_b = 0
    r = np.roots([-ma, -2 * (ma + mb), -mb])          # c_b/c_a
    return [np.array([1, x, -1 - x]) for x in r]
for m3 in ([1, 2, -3], [1, 1, -2], [2 + 1j, -0.7, -1.3 - 1j]):
    m = np.zeros(5, complex); m[:3] = m3; cp, cm_ = cpm(m[:3])
    N = np.zeros((2, 4, 5), complex); N[0][:, :3] = np.outer(chi(1), cp); N[1][:, :3] = np.outer(chi(3), cm_)
    e, Cb, lev, sv = defect(N)
    print('(v1) m = %s: c^+ c^- / m = %s; type V plane: defect dim %d, level err %.1e, residual vs C m %.1e, sl err %.1e' % (
        np.round(m[:3], 2), np.round(cp * cm_ / m[:3], 4), e, lev, chk_m(N, m), sl_check(N, trials=20)))
m = np.array([1, w, w * w, 0, 0]); mbar = np.array([1, w * w, w, 0, 0])
U = [np.array([1, 0, -1, 0.]), np.array([0, 1, 0, -1.])]
N = np.array([np.outer(u, mbar) for u in U]); e, Cb, lev, sv = defect(N)
print('(v2) isotropic m: U_2 (x) mbar: defect dim %d, level err %.1e, residual vs C m %.1e, sl err %.1e' % (e, lev, chk_m(N, m), sl_check(N, trials=20)))
worst = 0
for _ in range(20):
    m3 = cn(3); m3[2] = -m3[0] - m3[1]; Yp = cn(3, 4); Yp -= Yp.mean(1, keepdims=True); ma, mb, mc = m3
    ya = mc * Yp[1] + mb * Yp[2]; yb = mc * Yp[0] + ma * Yp[2]; yc = mb * Yp[0] + ma * Yp[1]
    u = np.cross(m3, cn(3)); d = lambda a, b: np.sum(a * b)
    lhs = u[0] * d(yb, yc) + u[1] * d(ya, yc) + u[2] * d(ya, yb); rhs = ma * mb * mc * sum(u[j] / m3[j] * d(Yp[j], Yp[j]) for j in range(3))
    worst = max(worst, abs(lhs - rhs))
print('(v3) 3-column diagonalisation identity: max error %.1e' % worst)
