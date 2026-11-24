import sys, os, itertools; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
"""calib_rad6.py -- CALIBRATION of the RATIONAL radical cell rc6 (R15.7) (gen_t22rad, R14.6) on a ROW-PERMUTED copy of the exact control K_2.
   K_2 itself has r_3 = 0; permuting rows 1..3 (row 0 fixed: the pivot (0,0), the 'ab' charts and the gauge entries (0,0), (0,3) keep their
   meaning, so the copy is again a point of case 9 at t = -1) moves a nonzero entry of r into row 3.  The copy is transformed to the radical
   normal form of rc4 (or rc5) and every equation of gen_t22rad.build(..., 'n3', rc, calib_rho1=True) is evaluated; perturbations must fail."""
import exactlib as X, gen_n1s, gen_n3, gen_t22rad, test_n3 as T
p = T.p; val = dict(T.val); val['mt'] = p - 1; case = gen_n1s.cases(2)[9]
cs = X.Consts(p); V = X.Vars(); V.new('mt'); B, ex, ells = gen_n3.nbasis(p, cs, case, V)
S = gen_n3.svectors(p, 0, V); Yold = []
for r in range(2):
    co = [V.new('w%d_%d' % (r, d)) for d in range(12)]
    Yold.append(X.madd_const_col(X.dc_matrix(co, p), S[r], 0, p))
names = V.names
ev = lambda q: X.peval(q, {i: val[n] for i, n in enumerate(names)}, p)
M = lambda A: [[ev(A[a][j]) for j in range(5)] for a in range(4)]
Ms = [M(B[0]), M(B[1]), M(Yold[0]), M(Yold[1])]
inv = lambda x: pow(x, p - 2, p); ip = lambda u, v: sum(x * y for x, y in zip(u, v)) % p
bcoef = lambda v: (v[0] % p, (v[0] + v[1]) % p, (-v[3]) % p)
rowsum = lambda A: [sum(A[a]) % p for a in range(4)]
ok_any = False
c1, c2, c3 = cs.chi1, cs.chi2, cs.chi3
w = lambda tau: [(c1[a] + 2 * tau * c2[a] - 2 * tau * tau * c3[a]) % p for a in range(4)]
wd = lambda tau: [(2 * c2[a] - 4 * tau * c3[a]) % p for a in range(4)]
for perm in ((0, 1, 2, 3), (0, 3, 2, 1)):
    P = [[A[perm[a]][j] for j in range(5)] for A in Ms for a in range(4)]
    Z0, Z1, Y1, Y2 = [P[4 * i:4 * i + 4] for i in range(4)]
    s1, s2 = rowsum(Y1), rowsum(Y2)
    G = [[ip(x, y) for y in (s1, s2)] for x in (s1, s2)]
    rho = [G[1][1], (-G[0][1]) % p] if (G[1][1] or G[0][1]) else [G[0][1], (-G[0][0]) % p]
    rvec = [(rho[0] * s1[a] + rho[1] * s2[a]) % p for a in range(4)]
    # coordinates of r in the chi basis: r = x1 chi1 + x2 chi2 + x3 chi3 (chi's are a basis of V); <chi1,chi3> = 4, <chi2,chi2> = 4
    x1 = ip(rvec, c3) * inv(4) % p; x2 = ip(rvec, c2) * inv(4) % p; x3 = ip(rvec, c1) * inv(4) % p
    assert all((x1 * c1[a] + x2 * c2[a] + x3 * c3[a] - rvec[a]) % p == 0 for a in range(4))
    if x1 == 0: print('perm %s: r || chi_3 (rc7) - skipped' % (perm,)); continue
    tau = x2 * inv(2 * x1) % p; lam = x1
    assert all((lam * w(tau)[a] - rvec[a]) % p == 0 for a in range(4)), 'r not on w(tau)'
    def gauge(Y):
        sv = rowsum(Y); cc_ = Y[0][3] * inv(Z1[0][3]) % p; Y = [[(Y[a][j] - cc_ * Z1[a][j]) % p for j in range(5)] for a in range(4)]
        d_ = (Y[0][0] - sv[0]) * inv(Z0[0][0]) % p; return [[(Y[a][j] - d_ * Z0[a][j]) % p for j in range(5)] for a in range(4)]
    Y1g, Y2g = gauge(Y1), gauge(Y2)
    il = inv(lam)
    Yr = [[(rho[0] * Y1g[a][j] + rho[1] * Y2g[a][j]) * il % p for j in range(5)] for a in range(4)]       # s(Yr) = w(tau)
    # Y_2': s = w'(tau) = a1 s1 + a2 s2 (solve in the 2-dim S)
    t_ = wd(tau); det = (s1[0] * s2[1] - s1[1] * s2[0]) % p
    a1 = (t_[0] * s2[1] - t_[1] * s2[0]) * inv(det) % p; a2 = (s1[0] * t_[1] - s1[1] * t_[0]) * inv(det) % p
    assert all((a1 * s1[a] + a2 * s2[a] - t_[a]) % p == 0 for a in range(4)), "w'(tau) not in S"
    Yd = [[(a1 * Y1g[a][j] + a2 * Y2g[a][j]) % p for j in range(5)] for a in range(4)]
    D1 = [[(Yr[a][j] - (w(tau)[a] if j == 0 else 0)) % p for j in range(5)] for a in range(4)]
    D2 = [[(Yd[a][j] - (t_[a] if j == 0 else 0)) % p for j in range(5)] for a in range(4)]
    v3 = [Z1[a][3] for a in range(4)]; half = (p + 1) // 2; wt = w(tau)
    assert [D1[a][3] for a in range(4)] == [half * (wt[a] - wt[0] * v3[a]) % p for a in range(4)], 'R13.5 formula fails'
    nn, polys = gen_t22rad.build(p, 'A', 9, 'n3', None, 6, calib_rho1=True)
    vv = {'mt': p - 1, 'al': 0, 'rtau': tau, 'a3': v3[1], 'b3': v3[2], 'a4': val['a4'], 'b4': val['b4']}
    for d in range(6):
        if 'u0_%d' % d in nn: vv['u0_%d' % d] = Z0[d % 3][d // 3]
        if 'y0_%d' % d in nn: vv['y0_%d' % d] = Z1[d % 3][d // 3]
    for t2 in range(2):
        for a in range(3): vv['w0_%d' % (3 * t2 + a)] = D1[a][t2]
    for a in range(3): vv['w0n4_%d' % a] = D1[a][4]
    for a in range(3):
        for q in range(4): vv['w1_%d' % (4 * a + q)] = D2[a][q]
    miss = [n_ for n_ in nn if n_ not in vv]; assert not miss, miss
    vi = {i: vv[n_] for i, n_ in enumerate(nn)}
    bad = sum(1 for q in polys if X.peval(q, vi, p) != 0)
    vj = dict(vi); kk = nn.index('rtau'); vj[kk] = (vj[kk] + 1) % p
    bad2 = sum(1 for q in polys if X.peval(q, vj, p) != 0)
    print('perm %s: K_2 copy in rc6 (tau = %d): %d of %d equations violated (expected 0); perturbed tau: %d violated' % (perm, tau, bad, len(polys), bad2))
    ok_any = ok_any or (bad == 0 and bad2 > 0)
print('CALIBRATION rc6', 'PASSED' if ok_any else 'FAILED')
