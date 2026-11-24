import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
"""rho1cell.py -- K-level decision of one rho = 1 item (gen_t22pc1 piece + word) whose N-system is not unit: S-cells 0, 1, 2 (old S-cells + Gram,
   gauge (0,0)/(0,3)), fine stages with extra filtering, GB of the N-system (file from nlam1, if present) inherited.  Item OK iff all three
   S-cells are UNIT.  usage: python3 -I rho1cell.py C CI PIECE UK DSPLIT WORD OUTPREFIX TMO [N_GB_FILE]"""
import subcut_fixed as subcut; sys.modules['subcut'] = subcut
import exactlib as X, gen_t22pc1 as G
p = 2147483629
chart, ci, pc, uk, ds, word, out, tmo = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4], sys.argv[5], sys.argv[6], sys.argv[7], float(sys.argv[8])
ds = None if ds == '-' else ds; word = None if word in ('-', 'm') else word
os.makedirs(os.path.dirname(out) or '.', exist_ok=True)
STAGES = [[0, 2], [1, 2], [0, 1, 2], [0, 3], [1, 3], [2, 3], [0, 1, 3], [0, 1, 2, 3]]
def readgb(fn):
    s = open(fn).read(); body = s[s.index('['):].strip().rstrip(':').strip()[1:-1]; return [x.strip() for x in body.split(',\n') if x.strip()]
def run_filtered(names, eqs, extra, stages, out, tmo, pre=()):
    vs = lambda q: {v for mon in q for v in mon}
    kv = set().union(*[vs(q) for q in eqs.values() if q]); xonly = set().union(*[vs(q) for q in extra]) - kv
    gbs = [((), list(pre))] if pre else []
    for k, S in enumerate(stages):
        xs = {X.XOFF + r for r in S}
        polys = [e for (i, xm), e in eqs.items() if e and set(xm) <= xs]
        allowed = (set().union(*[vs(q) for q in polys]) if polys else set()) | xonly
        ex = [q for q in extra if vs(q) <= allowed]
        prev = [g for (S0, G_) in gbs if set(S0) <= set(S) for g in G_]
        fn = '%s_st%d.ms' % (out, k); vn = subcut.used_names(names, polys + ex, prev)
        with open(fn, 'w') as f: f.write(','.join(vn) + '\n' + str(p) + '\n' + ',\n'.join([X.fmt_poly(q, names) for q in polys + ex] + prev) + '\n')
        G_, dt = subcut.msolve(fn, tmo)
        print('    stage %d S=%s: %d vars -> GB %d (%.1fs)%s' % (k, S, len(vn), len(G_), dt, '  UNIT' if G_ == ['1'] else ''), flush=True)
        gbs.append((S, G_))
        if G_ == ['1']: return 'UNIT'
    return 'NONUNIT'
pre = []
if len(sys.argv) > 9 and os.path.exists(sys.argv[9]) and '[' in open(sys.argv[9]).read(): pre = readgb(sys.argv[9])
res = []
for sc in (0, 1, 2):
    try:
        nm, eqs, extra = G.cellsystem(p, chart, ci, pc, uk, ds, word, sc)
        v = 'UNIT' if X.trivially_unit(extra) else run_filtered(nm, eqs, extra, STAGES, '%s_s%d' % (out, sc), tmo, pre=pre)
    except Exception as e_: v = 'FAIL(%s)' % type(e_).__name__
    res.append(v); print('  scell %d: %s' % (sc, v), flush=True)
print('VERDICT rho1cell %s c%d %s %s %s word %s: %s %s' % (chart, ci, pc, uk, ds or '-', word or 'm', 'OK' if all(r == 'UNIT' for r in res) else 'OPEN', res), flush=True)
