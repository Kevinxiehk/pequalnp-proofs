import sys, os, subprocess; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
"""nlam1.py -- N-level decision of ALL items of a rho = 1 case (9, 10, 11; chart C) with junk removal (gen_t22pc1, R18.3).
   Items: IV1 u_1:u_2 (16, lambda-words over the non-'0' k), Q2 u_0:u_1:u_2 (63 + det split nl/01/02/12), Q1a, Q1b with u_0 = 'ab' and
   u_1:u_2 (15 + 01/02/12 for ab:ab).  Each msolve call under rsscap (env NLAM_CAP, default 550 MB) and TMO.  A verdict line per item.
   usage: python3 -I nlam1.py C CI [TMO] [PIECES=IV1,Q2,Q1a,Q1b] [ITEMS=PIECE/UK/DS,...]   (ITEMS: only these items)"""
import exactlib as X, gen_t22pc1 as G
p = 2147483629; chart, ci = sys.argv[1], int(sys.argv[2]); tmo = sys.argv[3] if len(sys.argv) > 3 else '120'
pieces = (sys.argv[4] if len(sys.argv) > 4 else 'IV1,Q2,Q1a,Q1b').split(',')
od = '/home/kevxhk/work/L-gct-210/verifyfl/r12/nlam1'; os.makedirs(od, exist_ok=True)
ch = ('ab', 'z1', 'z2', '0')
def solve(names, polys, fn):
    if X.trivially_unit(polys): return 'UNIT(const)'
    X.write_msolve(fn, names, p, polys)
    if os.path.exists(fn + '.gb'): os.remove(fn + '.gb')
    r = subprocess.run(['python3', '-I', '/home/kevxhk/work/L-gct-210/verifyfl/r12/rsscap.py', os.environ.get('NLAM_CAP', '550'), tmo, '/usr/bin/msolve', '-g', '2', '-t', '1', '-f', fn, '-o', fn + '.gb'], capture_output=True, text=True)
    b = open(fn + '.gb').read() if os.path.exists(fn + '.gb') else ''
    if r.returncode or not b: return 'FAIL(cap/timeout)' if 'RSSCAP' in r.stdout else 'FAIL(rc%d)' % r.returncode
    return 'UNIT' if b[b.index('['):].strip().rstrip(':').strip()[1:-1].strip() == '1' else 'NONUNIT'
items = []
if 'IV1' in pieces: items += [('IV1', 'ab:%s:%s' % (a, b), None) for a in ch for b in ch]
if 'Q2' in pieces: items += [('Q2', '%s:%s:%s' % (a, b, c), None) for a in ch for b in ch for c in ch if (a, b, c) != ('ab', 'ab', 'ab')] + [('Q2', 'ab:ab:ab', d) for d in ('nl', '01', '02', '12')]
for q in ('Q1a', 'Q1b'):
    if q in pieces: items += [(q, 'ab:%s:%s' % (a, b), None) for a in ch for b in ch if (a, b) != ('ab', 'ab')] + [(q, 'ab:ab:ab', d) for d in ('01', '02', '12')]
if len(sys.argv) > 5:
    want = set(sys.argv[5].split(','))
    items = [it for it in items if '%s/%s/%s' % (it[0], it[1], it[2] or '-') in want]
nok = 0; opened = []
for pc, uk, ds in items:
    uks = uk.split(':')
    if pc == 'IV1':
        ks = [k for k in (1, 2) if uks[k] != '0']
        words = sorted({''.join(w[i] if (i + 1) in ks else 'A' for i in range(2)) for w in ('AA', 'AB', 'BA', 'BB')})
    else: words = [None]
    res = []
    for w in words:
        names, polys = G.nsystem(p, chart, ci, pc, uk, ds, w)
        fn = '%s/%s_c%d_%s_%s_%s_%s.ms' % (od, chart, ci, pc, uk.replace(':', ''), ds or 'x', w or 'm')
        res.append(solve(names, polys, fn))
    ok = all(r.startswith('UNIT') for r in res); nok += ok
    if not ok: opened.append('%s/%s/%s' % (pc, uk, ds or '-'))
    print('VERDICT nlam1 %s c%d %s %s %s: %s' % (chart, ci, pc, uk, ds or '-', 'N-UNIT' if ok else dict(zip([w or 'm' for w in words], res))), flush=True)
print('SUMMARY nlam1 %s c%d: %d/%d items N-UNIT; open: %s' % (chart, ci, nok, len(items), ' '.join(opened)), flush=True)
