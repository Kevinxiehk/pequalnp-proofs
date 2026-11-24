import sys, os, glob, time, subprocess; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
"""batch_items.py -- ONE big-slot job for a list of [T22] rho = 2 pieces (round 17, NOTES R17.3).  Per item (NB/NBARGS, e.g. pc/P1a/ab:ab:z1/-
   or t0c/ne), in this order, each msolve call under ulimit 2.5 GB (set by the caller) and its own timeout:
     (1) N-system (TN s).  UNIT -> item OK.
     (2) otherwise the open-chart radical cover with the early two-column Rabinowitsch (R16.2) and the xn extras, fine stages + extra filtering
         (as radcell3): rc0..rc3 with gam = 0, rc5, rc4 (each stage TS s).  Item OK iff every cell is UNIT (or RAB-UNIT).
   A verdict line per item and per cell is printed and flushed; at the end a summary.  Items run strictly sequentially.
   usage: python3 -I batch_items.py P C CI OUTDIR TN TS ITEM [ITEM ...]"""
import subcut_fixed as subcut; sys.modules['subcut'] = subcut
import exactlib as X, gen_t22rad as G, gen_n1s, gen_sym, gen_sym_n3
p, chart, ci, od, tn, ts = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), sys.argv[4], float(sys.argv[5]), float(sys.argv[6])
items = sys.argv[7:]; os.makedirs(od, exist_ok=True)
STAGES = [[0, 2], [1, 2], [0, 1, 2], [0, 3], [1, 3], [2, 3], [0, 1, 3], [0, 1, 2, 3]]
def readgb(fn):
    s = open(fn).read(); body = s[s.index('['):].strip().rstrip(':').strip()[1:-1]; return [x.strip() for x in body.split(',\n') if x.strip()]
def run_filtered(names, eqs, extra, stages, out, tmo, pre=()):
    vs = lambda q: {v for mon in q for v in mon}
    kv = set().union(*[vs(q) for q in eqs.values() if q])
    xonly = set().union(*[vs(q) for q in extra]) - kv
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
summary = []
for it in items:
    t0 = time.time(); nb, nba = it.split('/', 1)
    tag = '%s/b_%s_c%d_%s' % (od, chart, ci, it.replace('/', '_').replace(':', ''))
    cs = X.Consts(p); V = X.Vars(); t = V.new('mt')
    B, ex, ells = G.nbasis_any(p, cs, gen_n1s.cases(2)[ci], V, chart, nb, nba)
    polys = [q for q in gen_sym.equations_poly(B, gen_sym_n3.wpoly(p, chart, t), p) + list(ex) if q]
    if X.trivially_unit(polys): print('ITEM %s: UNIT (N constant)' % it, flush=True); summary.append((it, 'OK')); continue
    X.write_msolve(tag + '_N.ms', V.names, p, polys)
    try: GN, dt = subcut.msolve(tag + '_N.ms', tn); nv = 'UNIT' if GN == ['1'] else 'NONUNIT(%d)' % len(GN)
    except Exception as e_: GN = []; nv = 'FAIL(%s)' % type(e_).__name__
    print('ITEM %s: N-system %s' % (it, nv), flush=True)
    if GN == ['1']: summary.append((it, 'OK')); continue
    res = []
    for rc, gam in ((0, True), (1, True), (2, True), (3, True), (5, False), (4, False)):
        try:
            nm, eqs, extra = G.build(p, chart, ci, nb, nba, rc, keyed=True, xn=True, gam0=gam, rab=True)
            if X.trivially_unit(extra): v = 'UNIT'
            else: v = run_filtered(nm, eqs, extra, STAGES, '%s_rc%d%s' % (tag, rc, 'g' if gam else ''), ts, pre=GN)
        except Exception as e_: v = 'FAIL(%s)' % type(e_).__name__
        res.append(v); print('  %s rc%d%s: %s' % (it, rc, '+gam0' if gam else '', v), flush=True)
    ok = all(r == 'UNIT' for r in res)
    summary.append((it, 'OK' if ok else 'OPEN %s' % res))
    print('ITEM %s: %s (%.0f s)' % (it, 'OK' if ok else 'OPEN %s' % res, time.time() - t0), flush=True)
print('SUMMARY batch: %d/%d items OK' % (sum(1 for _, v in summary if v == 'OK'), len(summary)), flush=True)
for it, v in summary:
    if v != 'OK': print('  open: %s %s' % (it, v), flush=True)
