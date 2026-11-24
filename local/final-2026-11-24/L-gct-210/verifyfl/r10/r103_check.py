"""numerical check of R10.3: for Z on the split-B family (m = (1,2,-3,0,0), <z_j,z_j> = m_j, tau(z0 z1 z2) = 0), the LINEAR conditions on
Y = (y_0, y_1, y_2, 0, 0) (y_j in V): polarised Theta-relations <z_b,y_c> + <z_c,y_b> = 0 (3), the x^2 t tau-cubic (1), y_0 + y_1 + y_2 = omega (3)
have rank 7 on C^9 (y_j in V: 3 coordinates each), leaving a 2-dim affine family."""
import numpy as np, scipy.optimize as so, itertools
m = np.array([1., 2., -3.]); rng = np.random.default_rng(3)
Bv = np.array([[1, -1, 0, 0], [0, 1, -1, 0], [0, 0, 1, -1]], float).T        # basis of V (columns)
def zfam(x):
    c = x[:6] + 1j * x[6:]; z0 = Bv @ c[:3]; z1 = Bv @ c[3:]; return z0, z1, -z0 - z1
def res(x):
    z = zfam(x); r = np.array([z[0] @ z[0] - m[0], z[1] @ z[1] - m[1], z[2] @ z[2] - m[2], np.sum(z[0] * z[1] * z[2])]); return np.r_[r.real, r.imag]
def perm3(cols, i):
    rows = [r for r in range(4) if r != i]
    return sum(np.prod([cols[c][rows[k]] for k, c in enumerate(f)]) for f in itertools.permutations(range(3)))
for trial in range(3):
    x = so.least_squares(res, rng.normal(size=12), method='trf', xtol=1e-15, ftol=1e-15).x; z = zfam(x)
    c = np.array([perm3(z, i) for i in range(4)]); om = c - c.mean()
    rows = []; rhs = []
    def lin(f):   # f(y0, y1, y2) linear -> row over the 9 coordinates
        return np.array([f(*[Bv @ np.eye(9)[k][3 * j:3 * j + 3] for j in range(3)]) for k in range(9)])
    for (a, b, cc) in ((0, 1, 2), (1, 2, 0), (2, 0, 1)):
        rows.append(lin(lambda y0, y1, y2, b=b, cc=cc: z[b] @ [y0, y1, y2][cc] + z[cc] @ [y0, y1, y2][b])); rhs.append(0)
    rows.append(lin(lambda y0, y1, y2: np.sum(y0 * z[1] * z[2]) + np.sum(z[0] * y1 * z[2]) + np.sum(z[0] * z[1] * y2))); rhs.append(0)
    Ssum = lin(lambda y0, y1, y2: y0 + y1 + y2)                      # 9 x 4 -> coordinates in C^4 (sum-zero automatically)
    A = np.vstack(rows + [Ssum[:, :3].T])                             # first 3 coordinates of s determine s in V
    print('Z residual %.1e, |omega| %.2f, rank of the 7 linear conditions on C^9: %d (singular values %s)' % (np.abs(res(x)).max(), np.abs(om).max(), np.linalg.matrix_rank(A, 1e-9), ' '.join('%.1e' % v for v in np.linalg.svd(A, compute_uv=False))))
