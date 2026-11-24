import sys, os, glob; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
"""radcell3.py (= radcell2.py with FINE stages 02 | 12 | 012 | 03 | 13 | 23 | 013 | 0123) -- one N-piece of a rho = 2 [T22] case with the RADICAL S-cells rc0..rc3 (gen_t22rad, NOTES R13.4).
   Per radical cell: stages N+Y_1 | N+Y_2 | all (subcut_fixed.run; GB_N inherited from N_GB_FILE if it is a real msolve output, else the
   N-system is solved first with TMO); non-unit final stage -> Rabinowitsch test (+ urab*t*(t+1) - 1).
   The piece is OK iff all four radical cells are UNIT / RAB-UNIT.
   usage: python3 -I radcell.py P C CI NB NBARGS OUTPREFIX TMO [N_GB_FILE]   (NB in n3, t0c, t0b, pc; NBARGS '-' for n3)"""
import subcut_fixed as subcut; sys.modules['subcut'] = subcut
import exactlib as X, gen_t22rad as G
XN = True; STAGES = [[0, 2], [1, 2], [0, 1, 2], [0, 3], [1, 3], [2, 3], [0, 1, 3], [0, 1, 2, 3]]
RSPLIT = os.environ.get('RSPLIT') or None
PERM34 = os.environ.get('PERM34') == '1'
PERMP = os.environ.get('PERMP') == '1'
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
    if X.trivially_unit(polys): print('VERDICT radcell3 %s c%d %s %s: UNIT (N constant)' % (chart, ci, nb, nba), flush=True); sys.exit()
    X.write_msolve(out + '_N.ms', V.names, p, polys)
    try: GN, dt = subcut.msolve(out + '_N.ms', tmo)
    except Exception as e_: GN = []; print('  N-system FAIL(%s)' % type(e_).__name__, flush=True)
    if GN == ['1']: print('VERDICT radcell3 %s c%d %s %s: UNIT (no N)' % (chart, ci, nb, nba), flush=True); sys.exit()

def run_filtered(names, eqs, extra, p, stages, out, tmo, pre=()):
    """subcut.run with EXTRA FILTERING: stage S uses the keyed coefficients with x-monomial in S, the extra polynomials whose variables all
    occur among those or only in extra equations, and the GBs of earlier stages S' c S.  Every polynomial used lies in the ideal of the cell, so UNIT at any
    stage = UNIT of the cell (same argument as subcut.run)."""
    vs = lambda q: {v for mon in q for v in mon}
    kv = set().union(*[vs(q) for q in eqs.values() if q])
    xonly = set().union(*[vs(q) for q in extra]) - kv            # variables that occur only in extra equations (Rabinowitsch etc.)
    gbs = [((), list(pre))] if pre else []
    for k, S in enumerate(stages):
        xs = {X.XOFF + r for r in S}
        polys = [e for (i, xm), e in eqs.items() if e and set(xm) <= xs]
        allowed = (set().union(*[vs(q) for q in polys]) if polys else set()) | xonly
        ex = [q for q in extra if vs(q) <= allowed]
        prev = [g for (S0, G_) in gbs if set(S0) <= set(S) for g in G_]
        fn = '%s_st%d.ms' % (out, k); vn = subcut.used_names(names, polys + ex, prev)
        with open(fn, 'w') as f:
            f.write(','.join(vn) + '\n' + str(p) + '\n' + ',\n'.join([X.fmt_poly(q, names) for q in polys + ex] + prev) + '\n')
        G_, dt = subcut.msolve(fn, tmo)
        print('stage %d S=%s: %d polys + %d extra + %d inherited, %d vars -> GB %d elements (%.1fs)%s' % (k, S, len(polys), len(ex), len(prev), len(vn), len(G_), dt, '  UNIT' if G_ == ['1'] else ''), flush=True)
        gbs.append((S, G_))
        if G_ == ['1']: return 'UNIT'
    return 'NONUNIT'
def rab(tag):
    fs = sorted(glob.glob(tag + '_st*.ms.gb'), key=os.path.getmtime)
    g = readgb(fs[-1]); vn = open(fs[-1][:-3]).readline().strip().split(',')
    with open(tag + '_rab.ms', 'w') as f: f.write(','.join(vn + ['urab']) + '\n' + str(p) + '\n' + ',\n'.join(g + ['urab*mt^2+urab*mt-1']) + '\n')
    G2, dt = subcut.msolve(tag + '_rab.ms', tmo); return 'RAB-UNIT' if G2 == ['1'] else 'RAB-NONUNIT(%d)' % len(G2)
res = []
RCS = [int(x) for x in os.environ.get("RCS", "0,1,2,3").split(",")]
for rc in RCS:
    nm, eqs, extra = G.build(p, chart, ci, nb, nba, rc, keyed=True, xn=XN, rsplit=RSPLIT, perm34=PERM34, permP=PERMP)
    tg = '%s_rc%d%s%s%s' % (out, rc, RSPLIT or '', 'P' if PERM34 else '', 'Q' if PERMP else '')
    if X.trivially_unit(extra): res.append('UNIT'); continue
    try:
        v = run_filtered(nm, eqs, extra, p, STAGES, tg, tmo, pre=GN)
        if v == 'NONUNIT': v = rab(tg)
    except Exception as e_: v = 'FAIL(%s)' % type(e_).__name__
    res.append(v); print('  rc%d: %s' % (rc, v), flush=True)
ok = all(r in ('UNIT', 'RAB-UNIT') for r in res)
print('VERDICT radcell3 %s c%d %s %s rsplit=%s perm34=%s permP=%s: %s %s' % (chart, ci, nb, nba, RSPLIT, PERM34, PERMP, 'OK' if ok else 'OPEN', res), flush=True)
