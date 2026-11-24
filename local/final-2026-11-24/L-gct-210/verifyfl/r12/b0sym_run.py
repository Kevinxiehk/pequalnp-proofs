import sys, os, glob; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
"""b0sym_run.py -- SYM-M [T31] split B0, chart A (gen_sym_b0): Z-set GB first, then stages Z+Y_1 | Z+Y_2 | all (subcut_fixed.run, GB_Z
   inherited); non-unit final stage -> Rabinowitsch test (+ urab*t*(t+1) - 1, R11.6).   usage: python3 -I b0sym_run.py P R OUTPREFIX TMO   (env RAB=1: urt t (t+1) = 1 from the start, R16.2)"""
import subcut_fixed as subcut; sys.modules['subcut'] = subcut
import exactlib as X, gen_sym_b0 as G
p, R, out, tmo = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], float(sys.argv[4])
os.makedirs(os.path.dirname(out) or '.', exist_ok=True)
nm, eqs, extra, B = G.build(p, R, keyed=True)
if os.environ.get('RAB') == '1':
    # R16.2: two-column points t = 0, -1 excluded from the start (R11.6, chart A)
    nm = list(nm); u_ = len(nm); nm.append('urt'); it_ = nm.index('mt')
    extra = list(extra) + [X.padd(X.pmul({(u_,): 1}, X.pmul({(it_,): 1}, X.padd({(it_,): 1}, X.pconst(1, p), p), p), p), X.pconst(1, p), p, -1)]
zx = [q for q in extra if not any(nm[v].startswith('y') for mon in q for v in mon)]
zeq = [e for (i, xm), e in eqs.items() if e and set(xm) <= {X.XOFF}]
X.write_msolve(out + '_Z.ms', nm, p, zeq + zx)
try: GZ, dt = subcut.msolve(out + '_Z.ms', tmo); print('Z-set GB: %d elements (%.1fs)' % (len(GZ), dt), flush=True)
except Exception as ex: GZ = []; print('Z-set GB FAIL(%s)' % type(ex).__name__, flush=True)
if GZ == ['1']: print('VERDICT b0sym A R=%d: UNIT (no Z)' % R); sys.exit()
st = [[0, 1], [0, 2], [0, 1, 2]] if R == 2 else [[0, 1], [0, 2], [0, 3], [0, 1, 2], [0, 1, 2, 3]]
try:
    v = subcut.run(nm, eqs, extra, p, st, out, tmo, pre=GZ)
    if v == 'NONUNIT':
        fs = sorted(glob.glob(out + '_st*.ms.gb'), key=os.path.getmtime); s = open(fs[-1]).read()
        g = [x.strip() for x in s[s.index('['):].strip().rstrip(':').strip()[1:-1].split(',\n') if x.strip()]
        vn = open(fs[-1][:-3]).readline().strip().split(',')
        with open(out + '_rab.ms', 'w') as f: f.write(','.join(vn + ['urab']) + '\n' + str(p) + '\n' + ',\n'.join(g + ['urab*mt^2+urab*mt-1']) + '\n')
        G2, dt = subcut.msolve(out + '_rab.ms', tmo); v = 'NONUNIT -> ' + ('RAB-UNIT' if G2 == ['1'] else 'RAB-NONUNIT(%d)' % len(G2))
except Exception as ex: v = 'FAIL(%s)' % type(ex).__name__
print('VERDICT b0sym A R=%d: %s' % (R, v), flush=True)
