import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
"""calib_rad.py -- CALIBRATION of the radical S-cell construction (gen_t22rad.build, R13.4) on the exact two-column control K_2
   (case 9 = (2,1,(0,),0,'ab','ab'), chart A at t = -1; values test_n3.val in the old S-cell-0 coordinates).
   Transform K_2 to the radical form: r = radical of S (in the S-cell-0 basis), Y_1' = Y_1 + (rho_2/rho_1) Y_2 minus multiples of Z_1
   (column 3 -> 0) and Z_0 (N_P pivot entry -> 0); Y_2 unchanged (s_2 = b_2 + sbe b_3 is the rc0 complement).  Then every equation of
   gen_t22rad.build(..., 'n3', rc0, calib_rho1=True) must vanish at the transformed point; a perturbed point must violate some."""
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
Z0, Z1 = M(B[0]), M(B[1]); Y1, Y2 = M(Yold[0]), M(Yold[1]); s = [[ev(x) for x in S[r]] for r in range(2)]
ip = lambda u, v: sum(x * y for x, y in zip(u, v)) % p
G = [[ip(s[i], s[j]) for j in range(2)] for i in range(2)]
rho = [G[1][1], (-G[0][1]) % p]; assert all((G[i][0] * rho[0] + G[i][1] * rho[1]) % p == 0 for i in range(2)) and rho[0]
inv = lambda x: pow(x, p - 2, p)
r2 = rho[1] * inv(rho[0]) % p
Y1n = [[(Y1[a][j] + r2 * Y2[a][j]) % p for j in range(5)] for a in range(4)]
# (B1n), (B3n) with b_n(Y) = 2 y_n - s(Y) on the OLD basis of K_2 (checks the reading of b_n; n = 3 active, n = 4 inactive):
sY = [s[0], s[1]]; Ys = [Y1, Y2]
for n in (3, 4):
    bn = [[(2 * Ys[i][a][n] - sY[i][a]) % p for a in range(4)] for i in range(2)]
    B1 = all((ip(bn[i], bn[j]) - ip(sY[i], sY[j])) % p == 0 for i in range(2) for j in range(2))
    B3 = all(ip([Z1[a][n] for a in range(4)], bn[i]) == 0 for i in range(2))
    print('n = %d: (B1n) b_n^* g = s^* g: %s;  (B3n) <z_n, b_n(Y)> = 0: %s' % (n, B1, B3)); assert B1 and B3
# gauge normalisation (R13.5): subtract c Z_1 so that the entry (0, 3) of Y_1' is 0
c = Y1n[0][3] * inv(Z1[0][3]) % p; Y1n = [[(Y1n[a][j] - c * Z1[a][j]) % p for j in range(5)] for a in range(4)]
rvec = [(s[0][a] + r2 * s[1][a]) % p for a in range(4)]
D = [[(Y1n[a][j] - (rvec[a] if j == 0 else 0)) % p for j in range(5)] for a in range(4)]
d = D[0][0] * inv(Z0[0][0]) % p; Y1n = [[(Y1n[a][j] - d * Z0[a][j]) % p for j in range(5)] for a in range(4)]
D = [[(Y1n[a][j] - (rvec[a] if j == 0 else 0)) % p for j in range(5)] for a in range(4)]
v3v = [Z1[a][3] for a in range(4)]; half = (p + 1) // 2
c3 = [half * (rvec[a] - rvec[0] * v3v[a]) % p for a in range(4)]
print('column 3 of Y_1\':', [D[a][3] for a in range(4)], ' formula (r - r[0] v_3)/2:', c3, ' r - v_3:', [(rvec[a] - v3v[a]) % p for a in range(4)])
assert [D[a][3] for a in range(4)] == c3, 'R13.5 formula fails on K_2'
# rc0 coordinates: r = b1 + rrho b2 + rgam b3 with rvec = (1, rrho - 1, rgam - rrho, -rgam)
rrho = (rvec[1] + 1) % p; rgam = (-rvec[3]) % p; assert rvec[0] == 1 and (rvec[2] - (rgam - rrho)) % p == 0
nn, polys = gen_t22rad.build(p, 'A', 9, 'n3', None, 0, calib_rho1=True)
v2 = dict(val); v2.update({'rrho': rrho, 'rgam': rgam, 'rsig': val['sbe']})
for t_ in range(2):
    for a in range(3): v2['w0_%d' % (3 * t_ + a)] = D[a][t_]
for dd in range(12): v2['w1_%d' % dd] = val['w1_%d' % dd]
for a in range(3): v2['w0n4_%d' % a] = D[a][4]
vv = {i: v2[n] for i, n in enumerate(nn)}
bad = sum(1 for q in polys if X.peval(q, vv, p) != 0)
print('K_2 in radical cell rc0: %d of %d equations violated (expected 0)' % (bad, len(polys)))
vv2 = dict(vv); k = nn.index('w0_1'); vv2[k] = (vv2[k] + 1) % p
bad2 = sum(1 for q in polys if X.peval(q, vv2, p) != 0)
print('perturbed w0_1: %d violated (expected > 0)' % bad2)
vv3 = {i: v2[n] for i, n in enumerate(nn)}; vv3[nn.index('mt')] = 3
print('at t = 3: %d violated (expected > 0)' % sum(1 for q in polys if X.peval(q, vv3, p) != 0))
print('CALIBRATION', 'PASSED' if bad == 0 and bad2 > 0 else 'FAILED')

# ---- rc4 (open chart r_3 != 0, R14.6): r' = r / gam, s_2' = b_1 + sig b_2 (zero b_3-coefficient) ----
bcoef = lambda v: (v[0] % p, (v[0] + v[1]) % p, (-v[3]) % p)          # coefficients (c1, c2, c3) of v = c1 b1 + c2 b2 + c3 b3 (sum-zero v)
c1, c2, c3 = bcoef(rvec); assert c1 == 1
if c3 == 0:
    print('K_2 has r_3 = 0 (radical coefficient of b_3 is 0): K_2 is NOT in the open chart rc4/rc5 - rc4 not calibratable with K_2; consistent with gam0'); sys.exit()
ig = inv(c3); rp = [x * ig % p for x in rvec]
Y1p = [[Y1n[a][j] * ig % p for j in range(5)] for a in range(4)]       # radical element for r' (neutral-column formula is linear in r)
sb = val['sbe']; s2old = s[1]
k_ = sb * ig % p                                                        # x = s2old - k_ r has zero b3-coefficient
xv = [(s2old[a] - k_ * rvec[a]) % p for a in range(4)]; xb = bcoef(xv); assert xb[2] == 0 and xb[0] != 0
ix_ = inv(xb[0]); s2p = [x * ix_ % p for x in xv]; sigp = xb[1] * ix_ % p
Y2p = [[(Y2[a][j] - k_ * Y1n[a][j]) * ix_ % p for j in range(5)] for a in range(4)]
D1 = [[(Y1p[a][j] - (rp[a] if j == 0 else 0)) % p for j in range(5)] for a in range(4)]
D2 = [[(Y2p[a][j] - (s2p[a] if j == 0 else 0)) % p for j in range(5)] for a in range(4)]
nn4, polys4 = gen_t22rad.build(p, 'A', 9, 'n3', None, 4, calib_rho1=True)
v4 = dict(val); rb = bcoef(rp); v4.update({'ralp': rb[0], 'rbet': rb[1], 'rsig': sigp})
for t_ in range(2):
    for a in range(3): v4['w0_%d' % (3 * t_ + a)] = D1[a][t_]
for a in range(3):
    for q in range(4): v4['w1_%d' % (4 * a + q)] = D2[a][q]
for a in range(3): v4['w0n4_%d' % a] = D1[a][4]
vv4 = {i: v4[n] for i, n in enumerate(nn4)}
bad4 = sum(1 for q in polys4 if X.peval(q, vv4, p) != 0)
print('K_2 in the open radical chart rc4: %d of %d equations violated (expected 0)' % (bad4, len(polys4)))
vv5 = dict(vv4); kk = nn4.index('ralp'); vv5[kk] = (vv5[kk] + 1) % p
print('perturbed ralp: %d violated (expected > 0)' % sum(1 for q in polys4 if X.peval(q, vv5, p) != 0))
print('CALIBRATION rc4', 'PASSED' if bad4 == 0 else 'FAILED')
