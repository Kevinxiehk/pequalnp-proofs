import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
"""pc_nsweep.py -- N-systems only (no Y) for every item of the pieces P2 / P1a / P1b of a rho = 2 case (gen_t22pc): 63 u-triples + the det
   split ne/01/02/12 of ab:ab:ab.  An item whose N-system is UNIT is decided (no N in that item).  usage: P C CI OUTDIR TMO PIECES   (each msolve under rsscap.py: RSS <= 550 MB and TMO s; old .gb removed, rc and size checked)"""
import subcut_fixed as subcut; sys.modules['subcut'] = subcut
import exactlib as X, gen_t22pc as G, gen_t22rad as R, gen_n1s, gen_sym, gen_sym_n3
p, chart, ci, od, tmo, pieces = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), sys.argv[4], float(sys.argv[5]), sys.argv[6].split(',')
os.makedirs(od, exist_ok=True)
ch = ('ab', 'z1', 'z2', '0')
items = ['%s:%s:%s/-' % (a, b, c) for a in ch for b in ch for c in ch if (a, b, c) != ('ab', 'ab', 'ab')] + ['ab:ab:ab/%s' % d for d in ('ne', '01', '02', '12')]
for pc in pieces:
    st = {}
    for it in items:
        uk, ds = it.split('/')
        cs = X.Consts(p); V = X.Vars(); t = V.new('mt')
        B, ex, ells = R.nbasis_any(p, cs, gen_n1s.cases(2)[ci], V, chart, 'pc', '%s/%s/%s' % (pc, uk, ds))
        polys = [q for q in gen_sym.equations_poly(B, gen_sym_n3.wpoly(p, chart, t), p) + list(ex) if q]
        if X.trivially_unit(polys): v = 'UNIT(const)'
        else:
            fn = '%s/N_%s_%s_c%d_%s_%s.ms' % (od, pc, chart, ci, uk.replace(':', ''), ds if ds != '-' else 'x'); X.write_msolve(fn, V.names, p, polys)
            import subprocess
            if os.path.exists(fn + '.gb'): os.remove(fn + '.gb')
            rr = subprocess.run(['python3', '-I', '/home/kevxhk/work/L-gct-210/verifyfl/r12/rsscap.py', '550', str(tmo), '/usr/bin/msolve', '-g', '2', '-t', '1', '-f', fn, '-o', fn + '.gb'], capture_output=True, text=True)
            if rr.returncode != 0 or not os.path.exists(fn + '.gb') or os.path.getsize(fn + '.gb') == 0:
                v = 'FAIL(%s)' % ('cap/timeout' if 'RSSCAP' in rr.stdout else 'rc%d' % rr.returncode)
            else:
                body = open(fn + '.gb').read(); body = body[body.index('['):].strip().rstrip(':').strip()[1:-1]
                v = 'UNIT' if body.strip() == '1' else 'NONUNIT'
        st.setdefault(v, []).append(it)
        print('N %s %s c%d %s: %s' % (pc, chart, ci, it, v), flush=True)
    print('SUMMARY %s %s c%d: %s' % (pc, chart, ci, {k: len(v) for k, v in st.items()}), flush=True)
    for k in st:
        if not k.startswith('UNIT'): print('  %s: %s' % (k, ' '.join(st[k])), flush=True)
