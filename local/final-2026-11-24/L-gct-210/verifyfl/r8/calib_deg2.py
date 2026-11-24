import sys; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact')
"""Calibration of R8.1 / gen_t31e: (1) find numerically a 4-dim column-centred K of type (3,1) (Z doubly centred on P, s(Y_r) = b_r)
satisfying ONLY the degree-2 defect conditions q_j(Y) = vartheta(Y) m_j; (2) check the R7.5/R8.1 claims on it (Psi eigenvalues
-1/(4 m_j), A_k e_k = 0, A_n orthogonal, sum A_j = -3); (3) evaluate gen_t31e's polynomials (coefficients lifted to Q by rational
reconstruction) at the eigen-normalised point: (N1)-(N4) and the degree-2 coefficient equations must vanish; degree 3/4 need not."""
import numpy as np, scipy.optimize as so, itertools, exactlib as X, gen_t31e
m = np.array([1., 2., -3., 0., 0.]); rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
b = [np.array(v, float) for v in ([1, -1, 0, 0], [0, 1, -1, 0], [0, 0, 1, -1])]
def unpack(x):
    c = x[:len(x)//2] + 1j * x[len(x)//2:]
    z0 = np.r_[c[0:3], -c[0:3].sum()]; z1 = np.r_[c[3:6], -c[3:6].sum()]
    Z = np.zeros((4, 5), complex); Z[:, 0] = z0; Z[:, 1] = z1; Z[:, 2] = -z0 - z1
    Ys = []; o = 6
    for r in range(3):
        D = np.zeros((4, 5), complex); D[:3, :4] = c[o:o+12].reshape(3, 4); o += 12
        D[:3, 4] = -D[:3, :4].sum(1); D[3, :] = -D[:3, :].sum(0)
        Y = D.copy(); Y[:, 0] += b[r]; Ys.append(Y)
    Th = np.zeros((4, 4), complex); iu = np.triu_indices(4); Th[iu] = c[o:o+10]; Th = Th + Th.T - np.diag(np.diag(Th))
    return [Z] + Ys, Th
def Qpol(Xm, Ym, j):
    sx, sy = Xm.sum(1), Ym.sum(1); return Xm[:, j] @ Ym[:, j] - (sx @ Ym[:, j] + sy @ Xm[:, j]) / 2
def res(x):
    Bs, Th = unpack(x); out = []
    for r, s in itertools.combinations_with_replacement(range(4), 2):
        for j in range(5): out.append(Qpol(Bs[r], Bs[s], j) - m[j] * Th[r, s])
    out.append(Bs[0][:, 0] @ Bs[0][:, 0] - m[0])            # vartheta(Z) = 1
    out = np.array(out); return np.r_[out.real, out.imag]
n = 6 + 36 + 10; best = None
for trial in range(20):
    x0 = rng.normal(size=2 * n)
    r = so.least_squares(res, x0, method='trf', xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=5000)
    if np.abs(res(r.x)).max() < 1e-12: best = r.x; break
print('degree-2 solution found:', best is not None, 'after', trial + 1, 'starts; residual %.1e' % np.abs(res(best)).max())
Bs, Th = unpack(best); Z = Bs[0]
G = np.array([[bi @ bj for bj in b] for bi in b])
# K' and Psi
Yp = [Bs[r] - Th[r, 0] / Th[0, 0] * Z for r in (1, 2, 3)]
Thp = np.array([[Th[r, s] - Th[r, 0] * Th[s, 0] / Th[0, 0] for s in (1, 2, 3)] for r in (1, 2, 3)])
Psi = np.linalg.solve(G, Thp); ev, evec = np.linalg.eig(Psi)
print('eigenvalues of Psi:', np.sort_complex(np.round(ev, 10)), ' expected -1/(4 m_j):', sorted(-1 / (4 * m[:3])))
# eigen-normalised basis: e_k = eigenvector for lam_k = -1/(4 m_k), <e_k,e_k> = 1
E = []; Yk = []
for k in range(3):
    lam = -1 / (4 * m[k]); i = np.argmin(abs(ev - lam)); cvec = evec[:, i]
    ek = sum(cvec[r] * b[r] for r in range(3)); sc = np.sqrt(ek @ ek); cvec = cvec / sc; ek = ek / sc
    E.append(ek); Yk.append(sum(cvec[r] * Yp[r] for r in range(3)))
print('Gram of e_k (must be I):', np.round(np.array([[a @ c for c in E] for a in E]), 9).real.tolist())
beta = {(k, j): 2 * Yk[k][:, j] - E[k] for k in range(3) for j in range(5)}
print('|beta_{k,k}| = |A_k e_k| (must be 0):', [float('%.1e' % abs(beta[(k, k)]).max()) for k in range(3)])
A = [np.array([[0j] * 3] * 3) for _ in range(5)]
for j in range(5):
    cols = np.array([beta[(k, j)] for k in range(3)]).T            # 4x3, columns A_j e_k in C^4
    A[j] = cols
gr = lambda Mc: Mc.T @ Mc
print('A_n^T A_n for neutral n (must be I):', [np.round(gr(A[n]), 9).real.tolist() == np.eye(3).tolist() for n in (3, 4)])
print('sum_j A_j e_k = -3 e_k:', np.abs(sum(A[j] for j in range(5)) + 3 * np.array(E).T).max())
print('A_j^* z_j = 0:', max(abs(A[j].T @ Z[:, j]).max() for j in range(3)))
# evaluate gen_t31e polynomials, coefficients lifted to Q
p = 2147483629
def ratrec(a):
    a %= p; r0, r1, s0, s1 = p, a, 0, 1
    while r1 * r1 * 2 > p: q = r0 // r1; r0, r1, s0, s1 = r1, r0 - q * r1, s1, s0 - q * s1
    return r1 / s1
names, eqs, extra, Bp = gen_t31e.build(p, 'm12m3', [0, 1, 2], keyed=True)
val = {}
for k in range(3):
    for j in range(5):
        if j != k:
            for t, ch in enumerate('abc'): val['B%d%d%s' % (k, j, ch)] = beta[(k, j)][t]
for t, ch in enumerate('abc'): val['Za' + ch] = Z[t, 0]; val['Zb' + ch] = Z[t, 1]
vv = [val[nm] for nm in names]
def ev_poly(q): return sum(ratrec(c) * np.prod([vv[i] for i in mon]) for mon, c in q.items())
print('max |(N1)-(N4)| at the point:', max(abs(ev_poly(q)) for q in extra))
for d in (2, 3, 4):
    vals = [abs(ev_poly(q)) for (i, xm), q in eqs.items() if q and len(xm) == d]
    print('degree-%d coefficient equations: %d, max |value| = %.2e' % (d, len(vals), max(vals)))
