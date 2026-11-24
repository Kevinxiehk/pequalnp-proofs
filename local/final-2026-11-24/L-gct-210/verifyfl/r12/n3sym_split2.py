import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7')
"""n3sym_split2.py -- SYM-M [T22] hard N-case CI (rho = 2 or rho = 1 pivot 0), chart C, one S-cell, with the vartheta split on BOTH generators of N
   and a FINE staged cut (round 12, NOTES R12.1).
   Z_1, Z_2 = the generators of N in gen_n3.nbasis order (B[0], B[1]); (F2): <z_j,z_j> = vartheta(Z_r) m_j on the P-columns j = 0, 1, 2.
   chart A (m_0 = 1): den_r = <z_0,z_0>, num_r = <z_1,z_1>;  chart B (m_1 = 1): den_r = <z_1,z_1>, num_r = <z_0,z_0>.
   MODE = two letters (for Z_1, Z_2), each 'z' (den_r = 0) or 'n' (u_r den_r = 1 and num_r - t den_r = 0); the four modes cover the case.
   Stages (x-index sets; 0, 1 = N, 2, 3 = Y_1, Y_2): 0 | 1 | 01 | 02 | 12 | 012 | 03 | 13 | 23 | 013 | 0123; stage S uses the coefficients
   whose x-monomial lies in S, all extra equations, and the GBs of all earlier stages S' c S (subcut.run) => UNIT at a stage = UNIT of the cell.
   msolve via subcut_fixed (E-STALE-OUTPUT guard).   usage: python3 -I n3sym_split2.py P C CI SCELL MODE OUTDIR [TIMEOUT]"""
import subcut_fixed as subcut; sys.modules['subcut'] = subcut
import exactlib as X, exactlib_fixed; X.run_msolve = exactlib_fixed.run_msolve
import gen_n1s, gen_sym_n3
p, chart, ci, sc, mode, od = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5], sys.argv[6]
tmo = float(sys.argv[7]) if len(sys.argv) > 7 else 900
case = gen_n1s.cases(2)[ci]; os.makedirs(od, exist_ok=True); tag = '%s/s2%s_c%d_s%d_%s' % (od, chart, ci, sc, mode)
nm, eqs, extra = gen_sym_n3.build(p, chart, case, sc, keyed=True)
# rebuild the N generators exactly as gen_sym_n3.build does (same Vars order: 'mt' first, then gen_n3.nbasis)
import gen_n3
cs = X.Consts(p); V2 = X.Vars(); V2.new('mt'); B, _, _ = gen_n3.nbasis(p, cs, case, V2); assert V2.names == nm[:len(V2.names)]
it = nm.index('mt'); assert len(B) == 2
def ip(u, v):
    q = {}
    for a, b in zip(u, v): q = X.padd(q, X.pmul(a, b, p), p)
    return q
nm = list(nm); extra = list(extra)
for r in range(2):
    col = lambda j: [B[r][a][j] for a in range(4)]
    n00, n11 = ip(col(0), col(0)), ip(col(1), col(1))
    den, num = (n00, n11) if chart == 'A' else (n11, n00)
    if mode[r] == 'z': extra.append(den)
    else:
        u = len(nm); nm.append('usp%d' % r)
        extra.append(X.padd(X.pmul({(u,): 1}, den, p), X.pconst(1, p), p, -1)); extra.append(X.padd(num, X.pmul({(it,): 1}, den, p), p, -1))
extra = [e for e in extra if e]
if X.trivially_unit(extra): print('VERDICT n3sym-split2 %s case %d scell %d %s: UNIT (constant)' % (chart, ci, sc, mode)); sys.exit()
st = [[0], [1], [0, 1], [0, 2], [1, 2], [0, 1, 2], [0, 3], [1, 3], [2, 3], [0, 1, 3], [0, 1, 2, 3]]
try:
    v = subcut.run(nm, eqs, extra, p, st, tag, tmo)
except Exception as exn:
    v = 'FAIL(%s: %s)' % (type(exn).__name__, str(exn)[:60])
print('VERDICT n3sym-split2 %s case %d %s scell %d %s: %s' % (chart, ci, case, sc, mode, v), flush=True)
