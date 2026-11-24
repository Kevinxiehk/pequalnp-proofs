import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7')
"""dc_cut.py -- subsystem cut for one gen_dc.py case (any |supp m|): stages = all PLANE subsystems {g,h} of the k generators, then
   the full set; every stage inherits the GBs of earlier stages contained in it (subcut.run).  All polynomials lie in the ideal of the
   case, so the final verdict equals the verdict of the case.   usage: python3 -I dc_cut.py P MSPEC K IDX OUTPREFIX [timeout]"""
import exactlib as X, gen_dc, subcut, itertools
p, mspec, k, idx, out = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
tmo = float(sys.argv[6]) if len(sys.argv) > 6 else 1500
cs, m, W, P, Nt = gen_dc.setup(p, mspec); case = gen_dc.cases(k, P, Nt)[idx]
names, eqs, extra, B = gen_dc.build(p, mspec, case, keyed=True)
n0, p0 = gen_dc.build(p, mspec, case)
assert n0 == names and sorted(sorted(q.items()) for q in p0) == sorted(sorted(q.items()) for q in [e for e in eqs.values() if e] + extra)
# plane stages, the ones containing the LAST generator (a complement element, neutral column active) first; a failed stage
# (timeout / memory) is skipped, its GB simply not inherited (still sound)
planes = sorted(itertools.combinations(range(k), 2), key=lambda c: (k - 1 not in c, c))
G_ok = []; v = None
for st, S in enumerate([list(c) for c in planes] + [list(range(k))]):
    xs = {X.XOFF + r for r in S}
    polys = [e for (i, xm), e in eqs.items() if e and set(xm) <= xs] + list(extra)
    prev = [g for (S0, G) in G_ok if set(S0) <= set(S) for g in G]
    fn = '%s_st%d.ms' % (out, st); vn = subcut.used_names(names, polys, prev)
    with open(fn, 'w') as f:
        f.write(','.join(vn) + '\n' + str(p) + '\n' + ',\n'.join([X.fmt_poly(q, names) for q in polys] + prev) + '\n')
    try:
        G, dt = subcut.msolve(fn, tmo if len(S) == k else min(tmo, 900))
    except Exception as ex:
        print('stage %d S=%s: FAILED (%s), skipped' % (st, S, type(ex).__name__), flush=True); continue
    print('stage %d S=%s: %d polys + %d inherited -> GB %d elements (%.1fs)%s' % (st, S, len(polys), len(prev), len(G), dt, '  UNIT' if G == ['1'] else ''), flush=True)
    if G == ['1']: v = 'UNIT'; break
    G_ok.append((S, G))
    if len(S) == k: v = 'NONUNIT'
if v is None: v = 'FAIL'
print('VERDICT dc_cut %s idx=%d case=%s p=%d: %s' % (mspec, idx, case, p, v), flush=True)
