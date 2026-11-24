import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
"""t0_cell.py: SYM-M [T22] rho = 2 N-case CI, piece (IV) vartheta == 0 (gen_t22t0), chart C: for every u-chart pair (or the listed ones)
   N-system GB, then per S-cell the staged cut N+Y_1 | N+Y_2 | all (subcut_fixed.run, GB_N inherited).  A cell that is not UNIT gets the
   Rabinowitsch test (R11.6): its final-stage GB + urab*t*(t+1) - 1.   usage: P C CI OUTDIR TMO [u0:u1,...]"""
import subcut_fixed as subcut; sys.modules['subcut'] = subcut
import exactlib as X, gen_t22t0 as G
p, chart, ci, od, tmo = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), sys.argv[4], float(sys.argv[5]); os.makedirs(od, exist_ok=True)
pairs = [tuple(s.split(':')) for s in sys.argv[6].split(',')] if len(sys.argv) > 6 else [(a, b) for a in ('ab', 'z1', 'z2', '0') for b in ('ab', 'z1', 'z2', '0')]
def rab(tag, names):
    """final-stage GB + urab*mt*(mt+1) - 1"""
    import glob
    fs = sorted(glob.glob(tag + '_st*.ms.gb'), key=os.path.getmtime)
    s = open(fs[-1]).read(); body = s[s.index('['):].strip().rstrip(':').strip()[1:-1]; g = [x.strip() for x in body.split(',\n') if x.strip()]
    vn = open(fs[-1][:-3]).readline().strip().split(',')
    fn = tag + '_rab.ms'
    with open(fn, 'w') as f: f.write(','.join(vn + ['urab']) + '\n' + str(p) + '\n' + ',\n'.join(g + ['urab*mt^2+urab*mt-1']) + '\n')
    G2, dt = subcut.msolve(fn, tmo); return 'RAB-UNIT' if G2 == ['1'] else 'RAB-NONUNIT(%d)' % len(G2)
allv = []
for u0, u1 in pairs:
    names, polys = G.build(p, chart, ci, u0, u1, None)
    tg = '%s/t0_%s_c%d_%s_%s' % (od, chart, ci, u0, u1)
    if X.trivially_unit(polys): print('VERDICT t0 %s c%d %s %s: UNIT (N constant)' % (chart, ci, u0, u1), flush=True); allv.append('UNIT'); continue
    X.write_msolve(tg + '_N.ms', names, p, polys)
    try: GN, dt = subcut.msolve(tg + '_N.ms', tmo)
    except Exception as ex: GN = []; print('  N-system FAIL(%s)' % type(ex).__name__, flush=True)
    if GN == ['1']: print('VERDICT t0 %s c%d %s %s: UNIT (no N)' % (chart, ci, u0, u1), flush=True); allv.append('UNIT'); continue
    res = []
    for s in (0, 1, 2):
        nm, eqs, extra = G.build(p, chart, ci, u0, u1, s, keyed=True)
        try:
            v = subcut.run(nm, eqs, extra, p, [[0, 1, 2], [0, 1, 3], [0, 1, 2, 3]], '%s_s%d' % (tg, s), tmo, pre=GN)
            if v == 'NONUNIT': v = rab('%s_s%d' % (tg, s), nm)
        except Exception as ex: v = 'FAIL(%s)' % type(ex).__name__
        res.append(v)
    ok = all(r in ('UNIT', 'RAB-UNIT') for r in res); allv.append('UNIT' if ok else 'X')
    print('VERDICT t0 %s c%d %s %s: %s %s' % (chart, ci, u0, u1, 'OK' if ok else 'OPEN', res), flush=True)
print('SUMMARY t0 %s c%d: %d/%d pairs OK' % (chart, ci, allv.count('UNIT'), len(allv)))
