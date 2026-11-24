import sys, os, glob; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
# VOID (round 13, R13.5): the radical equations here use columns 3, 4 of Y_rad = 0, which is wrong (b_n(Y) = 2 y_n - s(Y)); use radcell.py / gen_t22rad.
"""pc_cell.py -- SYM-M [T22] rho = 2 N-case CI, chart C: the pieces P2 / P1a / P1b of gen_t22pc (round 13, NOTES R13.2).
   ITEMS = comma list of PIECE/U0:U1:U2/DSPLIT (DSPLIT '-' = none), e.g. P2/ab:z1:0/-,P2/ab:ab:ab/ne.
   Per item: N-system GB (TMO), then S-cell 0 in BOTH radical charts r1, r2 (R13.1), S-cells 1 and 2 plain; stages N+Y_1 | N+Y_2 | all
   (subcut_fixed.run, GB_N inherited).  A non-unit final stage gets the Rabinowitsch test (+ urab*t*(t+1) - 1, R11.6).
   An item is OK iff every S-cell (both radical charts for S-cell 0) is UNIT or RAB-UNIT.
   usage: python3 -I pc_cell.py P C CI OUTDIR TMO ITEMS"""
import subcut_fixed as subcut; sys.modules['subcut'] = subcut
import exactlib as X, gen_t22pc as G
p, chart, ci, od, tmo, items = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), sys.argv[4], float(sys.argv[5]), sys.argv[6].split(',')
os.makedirs(od, exist_ok=True)
def rab(tag):
    fs = sorted(glob.glob(tag + '_st*.ms.gb'), key=os.path.getmtime)
    s = open(fs[-1]).read(); body = s[s.index('['):].strip().rstrip(':').strip()[1:-1]; g = [x.strip() for x in body.split(',\n') if x.strip()]
    vn = open(fs[-1][:-3]).readline().strip().split(',')
    fn = tag + '_rab.ms'
    with open(fn, 'w') as f: f.write(','.join(vn + ['urab']) + '\n' + str(p) + '\n' + ',\n'.join(g + ['urab*mt^2+urab*mt-1']) + '\n')
    G2, dt = subcut.msolve(fn, tmo); return 'RAB-UNIT' if G2 == ['1'] else 'RAB-NONUNIT(%d)' % len(G2)
nok = 0
for it in items:
    piece, uk, ds = it.split('/'); ds = None if ds == '-' else ds
    tg = '%s/pc_%s_c%d_%s_%s_%s' % (od, chart, ci, piece, uk.replace(':', ''), ds or 'x')
    names, polys = G.build(p, chart, ci, piece, uk, ds, None)
    if X.trivially_unit(polys): print('VERDICT pc %s c%d %s: UNIT (N constant)' % (chart, ci, it), flush=True); nok += 1; continue
    X.write_msolve(tg + '_N.ms', names, p, polys)
    try: GN, dt = subcut.msolve(tg + '_N.ms', tmo)
    except Exception as ex: GN = []; print('  %s N-system FAIL(%s)' % (it, type(ex).__name__), flush=True)
    if GN == ['1']: print('VERDICT pc %s c%d %s: UNIT (no N)' % (chart, ci, it), flush=True); nok += 1; continue
    res = []
    for sc, rad in ((0, 'r1'), (0, 'r2'), (1, None), (2, None)):
        nm, eqs, extra = G.build(p, chart, ci, piece, uk, ds, sc, rad=rad, keyed=True)
        t2 = '%s_s%d%s' % (tg, sc, rad or '')
        try:
            v = subcut.run(nm, eqs, extra, p, [[0, 1, 2], [0, 1, 3], [0, 1, 2, 3]], t2, tmo, pre=GN)
            if v == 'NONUNIT': v = rab(t2)
        except Exception as ex: v = 'FAIL(%s)' % type(ex).__name__
        res.append(v)
    ok = all(r in ('UNIT', 'RAB-UNIT') for r in res); nok += ok
    print('VERDICT pc %s c%d %s: %s %s' % (chart, ci, it, 'OK' if ok else 'OPEN', res), flush=True)
print('SUMMARY pc %s c%d: %d/%d items OK' % (chart, ci, nok, len(items)))
