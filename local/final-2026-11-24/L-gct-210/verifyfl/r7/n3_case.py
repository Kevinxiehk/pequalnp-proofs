import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7')
"""n3_case.py -- [T22] for one N-case (gen_n1s k = 2 case index CI), all three S-cells, with the N-system GB computed ONCE:
   GB_N := GB of gen_n1s.build((2,...)) (the 2-dim doubly centred system; its variable names coincide with those of gen_n3.nbasis);
   UNIT => no N of this case => all S-cells unit.  Otherwise per S-cell: stages N+Y1, N+Y2, all, each inheriting GB_N (subcut.run).
   usage: python3 -I n3_case.py P MSPEC CI OUTDIR [timeout]"""
import exactlib as X, gen_n1s, gen_n3, subcut
p = int(sys.argv[1]); mspec = sys.argv[2]; ci = int(sys.argv[3]); od = sys.argv[4]; tmo = float(sys.argv[5]) if len(sys.argv) > 5 else 900
case = gen_n1s.cases(2)[ci]; tag = '%s/%s_c%d' % (od, mspec, ci)
names, polys = gen_n1s.build(p, mspec, case)
if X.trivially_unit(polys): print('VERDICT n3 case %d %s m=%s p=%d: UNIT (N-system constant)' % (ci, case, mspec, p)); sys.exit()
cs = X.Consts(p); m, W = X.parse_m(mspec, cs); V = X.Vars()
B, ex, ells = gen_n3.nbasis(p, cs, case, V)
keq = X.equations(B, W, p, keyed=True)
assert V.names == names and sorted(sorted(q.items()) for q in polys) == sorted(sorted(q.items()) for q in [e for e in keq.values() if e] + ex)
import time; t0 = time.time()
X.write_msolve(tag + '_Nd.ms', names, p, polys)
try:
    GD, dtd = subcut.msolve(tag + '_Nd.ms', float(sys.argv[6]) if len(sys.argv) > 6 else 120); vN = 'UNIT' if GD == ['1'] else 'NONUNIT'; gbfile = tag + '_Nd.ms.gb'
    print('N-system direct: %d elements (%.1fs)' % (len(GD), dtd), flush=True)
except Exception:
    print('N-system direct: timeout -> no N-GB; going straight to N + Y stages', flush=True)
    vN = 'SKIP'
if vN == 'SKIP': GN = []
else:
    s = open(gbfile).read() if vN != 'UNIT' else ''
    GN = ['1'] if vN == 'UNIT' else [x.strip() for x in s[s.index('['):].strip().rstrip(':').strip()[1:-1].split(',\n') if x.strip()]
print('N-system %s: %d vars, GB %d elements (%.1fs)' % (case, len(names), len(GN), time.time() - t0), flush=True)
if GN == ['1']: print('VERDICT n3 case %d %s m=%s p=%d: UNIT (no N)' % (ci, case, mspec, p)); sys.exit()
res = []
for s in (0, 1, 2):
    nm, eqs, extra = gen_n3.build(p, mspec, case, s, keyed=True)
    assert nm[:len(names)] == names
    v = subcut.run(nm, eqs, extra, p, [[0, 1, 2], [0, 1, 3], [0, 1, 2, 3]], '%s_s%d' % (tag, s), tmo, pre=GN); res.append(v)
    print('  scell %d: %s' % (s, v), flush=True)
print('VERDICT n3 case %d %s m=%s p=%d: %s' % (ci, case, mspec, p, 'UNIT' if all(r == 'UNIT' for r in res) else 'NONUNIT %s' % res))
