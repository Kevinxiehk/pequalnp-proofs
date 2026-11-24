import sys, os, glob; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
"""radcell.py -- one N-piece of a rho = 2 [T22] case with the RADICAL S-cells rc0..rc3 (gen_t22rad, NOTES R13.4).
   Per radical cell: stages N+Y_1 | N+Y_2 | all (subcut_fixed.run; GB_N inherited from N_GB_FILE if it is a real msolve output, else the
   N-system is solved first with TMO); non-unit final stage -> Rabinowitsch test (+ urab*t*(t+1) - 1).
   The piece is OK iff all four radical cells are UNIT / RAB-UNIT.
   usage: python3 -I radcell.py P C CI NB NBARGS OUTPREFIX TMO [N_GB_FILE]   (NB in n3, t0c, t0b, pc; NBARGS '-' for n3)"""
import subcut_fixed as subcut; sys.modules['subcut'] = subcut
import exactlib as X, gen_t22rad as G
p, chart, ci, nb, nba, out, tmo = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5], sys.argv[6], float(sys.argv[7])
nba = None if nba == '-' else nba
os.makedirs(os.path.dirname(out) or '.', exist_ok=True)
def readgb(fn):
    s = open(fn).read(); body = s[s.index('['):].strip().rstrip(':').strip()[1:-1]; return [x.strip() for x in body.split(',\n') if x.strip()]
GN = []
if len(sys.argv) > 8 and os.path.exists(sys.argv[8]) and '[' in open(sys.argv[8]).read(): GN = readgb(sys.argv[8])
else:
    cs = X.Consts(p); V = X.Vars(); t = V.new('mt'); import gen_n1s, gen_sym_n3, gen_sym
    B, ex, ells = G.nbasis_any(p, cs, gen_n1s.cases(2)[ci], V, chart, nb, nba)
    polys = [q for q in gen_sym.equations_poly(B, gen_sym_n3.wpoly(p, chart, t), p) + list(ex) if q]
    if X.trivially_unit(polys): print('VERDICT radcell %s c%d %s %s: UNIT (N constant)' % (chart, ci, nb, nba), flush=True); sys.exit()
    X.write_msolve(out + '_N.ms', V.names, p, polys)
    try: GN, dt = subcut.msolve(out + '_N.ms', tmo)
    except Exception as e_: GN = []; print('  N-system FAIL(%s)' % type(e_).__name__, flush=True)
    if GN == ['1']: print('VERDICT radcell %s c%d %s %s: UNIT (no N)' % (chart, ci, nb, nba), flush=True); sys.exit()
def rab(tag):
    fs = sorted(glob.glob(tag + '_st*.ms.gb'), key=os.path.getmtime)
    g = readgb(fs[-1]); vn = open(fs[-1][:-3]).readline().strip().split(',')
    with open(tag + '_rab.ms', 'w') as f: f.write(','.join(vn + ['urab']) + '\n' + str(p) + '\n' + ',\n'.join(g + ['urab*mt^2+urab*mt-1']) + '\n')
    G2, dt = subcut.msolve(tag + '_rab.ms', tmo); return 'RAB-UNIT' if G2 == ['1'] else 'RAB-NONUNIT(%d)' % len(G2)
res = []
for rc in range(4):
    nm, eqs, extra = G.build(p, chart, ci, nb, nba, rc, keyed=True)
    tg = '%s_rc%d' % (out, rc)
    if X.trivially_unit(extra): res.append('UNIT'); continue
    try:
        v = subcut.run(nm, eqs, extra, p, [[0, 1, 2], [0, 1, 3], [0, 1, 2, 3]], tg, tmo, pre=GN)
        if v == 'NONUNIT': v = rab(tg)
    except Exception as e_: v = 'FAIL(%s)' % type(e_).__name__
    res.append(v); print('  rc%d: %s' % (rc, v), flush=True)
ok = all(r in ('UNIT', 'RAB-UNIT') for r in res)
print('VERDICT radcell %s c%d %s %s: %s %s' % (chart, ci, nb, nba, 'OK' if ok else 'OPEN', res), flush=True)
