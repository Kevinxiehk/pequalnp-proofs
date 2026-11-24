"""numerical: rank of the first-order map L(Z) : A_0 (column-centred 4x5, dim 15) -> coefficients of x^d eps (d = 1,2,3) of R_i(xZ + eps Y),
for Z on the split-B family (Z doubly centred on P = {0,1,2}, vartheta(Z) = 1, tau(z0 z1 z2) = 0).  K c ker L(Z) and Z in ker L(Z)."""
import numpy as np, itertools, scipy.optimize as so, sys
m = np.array([1., 2., -3., 0., 0.]) if len(sys.argv) < 2 else np.array(eval(sys.argv[1]), complex)
W = [np.eye(5)[3], np.eye(5)[4], np.r_[-m[1], m[0], 0, 0, 0], np.r_[-m[2], 0, m[0], 0, 0]]
def perm(M):
    n = M.shape[0]; return sum(np.prod([M[i, f[i]] for i in range(n)]) for f in itertools.permutations(range(n)))
def C(Y): return np.array([perm(np.ones((4, 4)) + np.delete(Y, j, axis=1)) for j in range(5)])
def R(Y): return np.array([w @ (C(Y) - 24) for w in W])
rng = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 0)
def zfam(x):
    c = x[:6] + 1j * x[6:]; z0 = np.r_[c[:3], -c[:3].sum()]; z1 = np.r_[c[3:], -c[3:].sum()]; z2 = -z0 - z1
    return z0, z1, z2
def res(x):
    z0, z1, z2 = zfam(x); r = np.array([z0 @ z0 - m[0], z1 @ z1 - m[1], z2 @ z2 - m[2], np.sum(z0 * z1 * z2)]); return np.r_[r.real, r.imag]
basisA = []
for c in range(5):
    for a in range(3):
        Y = np.zeros((4, 5)); Y[a, c] = 1; Y[3, c] = -1; basisA.append(Y)
xs = np.array([0.7, -1.3, 2.1, 0.4 + 0.9j, -0.6 - 1.1j])
for trial in range(4):
    r = so.least_squares(res, rng.normal(size=12), method='trf', xtol=1e-15, ftol=1e-15, gtol=1e-15)
    z0, z1, z2 = zfam(r.x); Z = np.zeros((4, 5), complex); Z[:, 0], Z[:, 1], Z[:, 2] = z0, z1, z2
    assert np.abs(R(Z)).max() < 1e-8, 'Z alone must have defect'
    rows = []
    eps = 1e-6
    for Yb in basisA:
        # derivative in eps by central difference of complex-analytic R (perm is polynomial): exact up to eps^2
        vals = np.array([(R(x * Z + eps * Yb) - R(x * Z - eps * Yb)) / (2 * eps) for x in xs])   # 5 x 4
        V = np.vander(xs, 4, increasing=True)                     # degrees 0..3
        coef = np.linalg.lstsq(V, vals, rcond=None)[0]            # 4 x 4 : degree x i
        rows.append(coef[1:].ravel())
    L = np.array(rows).T                                           # 12 x 15
    s = np.linalg.svd(L, compute_uv=False)
    print('Z residual %.1e; singular values of L(Z) (12 x 15):' % np.abs(res(r.x)).max(), ' '.join('%.2e' % v for v in s))
