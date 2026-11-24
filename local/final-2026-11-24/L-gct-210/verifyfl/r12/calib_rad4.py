import sys, os, itertools; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
"""calib_rad4.py -- CALIBRATION of the OPEN radical chart rc4/rc5 (gen_t22rad, R14.6) on a ROW-PERMUTED copy of the exact control K_2.
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
for perm in ((0, 3, 2, 1), (0, 1, 3, 2), (0, 2, 3, 1), (0, 3, 1, 2), (0, 2, 1, 3)):
    P = [[A[perm[a]][j] for j in range(5)] for A in Ms for a in range(4)]
    Z0, Z1, Y1, Y2 = [P[4 * i:4 * i + 4] for i in range(4)]
    s1, s2 = rowsum(Y1), rowsum(Y2)
    G = [[ip(x, y) for y in (s1, s2)] for x in (s1, s2)]
    rho = [G[1][1], (-G[0][1]) % p] if (G[1][1] or G[0][1]) else [G[0][1], (-G[0][0]) % p]
    rvec = [(rho[0] * s1[a] + rho[1] * s2[a]) % p for a in range(4)]; Yr = [[(rho[0] * Y1[a][j] + rho[1] * Y2[a][j]) % p for j in range(5)] for a in range(4)]
    c = bcoef(rvec)
    if c[2] == 0: continue
    ig = inv(c[2]); rvec = [x * ig % p for x in rvec]; Yr = [[x * ig % p for x in row] for row in Yr]
    # radical normalisation: gauge entry (0,3) via Z_1 (column 3 = v_3, v_3[0] = 1), N_P pivot entry (0,0) of the D-part via Z_0
    cc = Yr[0][3] * inv(Z1[0][3]) % p; Yr = [[(Yr[a][j] - cc * Z1[a][j]) % p for j in range(5)] for a in range(4)]
    D = [[(Yr[a][j] - (rvec[a] if j == 0 else 0)) % p for j in range(5)] for a in range(4)]
    dd = D[0][0] * inv(Z0[0][0]) % p; Yr = [[(Yr[a][j] - dd * Z0[a][j]) % p for j in range(5)] for a in range(4)]
    D1 = [[(Yr[a][j] - (rvec[a] if j == 0 else 0)) % p for j in range(5)] for a in range(4)]
    v3 = [Z1[a][3] for a in range(4)]; half = (p + 1) // 2
    assert [D1[a][3] for a in range(4)] == [half * (rvec[a] - rvec[0] * v3[a]) % p for a in range(4)], 'R13.5 formula fails'
    # s_2: element of S with zero b3-coefficient, then Y_2 = combination (keeps the Y-gauge entries (0,0), (0,3) zero: both Y's have them 0)
    # make the old Y's gauge-normalised first (entries (0,3) via Z_1, D-part (0,0) via Z_0)
    def gauge(Y):
        sv = rowsum(Y); cc_ = Y[0][3] * inv(Z1[0][3]) % p; Y = [[(Y[a][j] - cc_ * Z1[a][j]) % p for j in range(5)] for a in range(4)]
        Dg = (Y[0][0] - sv[0]) % p; d_ = Dg * inv(Z0[0][0]) % p; return [[(Y[a][j] - d_ * Z0[a][j]) % p for j in range(5)] for a in range(4)]
    Y1g, Y2g = gauge(Y1), gauge(Y2)
    # choose x in span(s1, s2) with zero b3-coefficient, independent of r
    k1, k2 = bcoef(s1)[2], bcoef(s2)[2]
    xv_c = (k2, (-k1) % p)                                   # k2 s1 - k1 s2 has zero b3-coefficient
    Yx = [[(xv_c[0] * Y1g[a][j] + xv_c[1] * Y2g[a][j]) % p for j in range(5)] for a in range(4)]; xv = rowsum(Yx)
    xb = bcoef(xv); assert xb[2] == 0
    if xb[0] != 0: rc = 4; sc = inv(xb[0]); sig = xb[1] * sc % p
    else: rc = 5; sc = inv(xb[1]); sig = None
    Yx = [[x * sc % p for x in row] for row in Yx]; s2p = rowsum(Yx)
    D2 = [[(Yx[a][j] - (s2p[a] if j == 0 else 0)) % p for j in range(5)] for a in range(4)]
    nn, polys = gen_t22rad.build(p, 'A', 9, 'n3', None, rc, calib_rho1=True)
    # values: N-variables from the permuted Z_0, Z_1 (dcsub coordinates: entry (a, t) = co[3t + a]); a3, b3 from v_3; al = 0
    vv = {'mt': p - 1, 'al': 0}
    rb = bcoef(rvec); vv.update({'ralp': rb[0], 'rbet': rb[1]})
    if sig is not None: vv['rsig'] = sig
    vv['a3'], vv['b3'] = v3[1], v3[2]
    v4 = None
    for n_ in nn:
        if n_ in ('a4', 'b4'): vv[n_] = val[n_]          # col 4 inactive (al = 0): v_4 arbitrary in its chart; keep K_2's value
    for d in range(6):
        if 'u0_%d' % d in nn: vv['u0_%d' % d] = Z0[d % 3][d // 3]
        if 'y0_%d' % d in nn: vv['y0_%d' % d] = Z1[d % 3][d // 3]
    for t_ in range(2):
        for a in range(3): vv['w0_%d' % (3 * t_ + a)] = D1[a][t_]
    for a in range(3): vv['w0n4_%d' % a] = D1[a][4]
    for a in range(3):
        for q in range(4): vv['w1_%d' % (4 * a + q)] = D2[a][q]
    miss = [n_ for n_ in nn if n_ not in vv]
    assert not miss, miss
    val_i = {i: vv[n_] for i, n_ in enumerate(nn)}
    bad = sum(1 for q in polys if X.peval(q, val_i, p) != 0)
    val_j = dict(val_i); kk = nn.index('ralp'); val_j[kk] = (val_j[kk] + 1) % p
    bad2 = sum(1 for q in polys if X.peval(q, val_j, p) != 0)
    print('row permutation %s: K_2 copy lies in rc%d; %d of %d equations violated (expected 0); perturbed ralp: %d violated' % (perm, rc, bad, len(polys), bad2))
    ok_any = ok_any or (bad == 0 and bad2 > 0)
print('CALIBRATION rc4/rc5', 'PASSED' if ok_any else 'FAILED')
