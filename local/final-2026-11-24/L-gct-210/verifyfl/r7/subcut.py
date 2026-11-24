import sys, os, subprocess, time; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact')
"""subcut.py -- staged SUBSYSTEM CUT for the typed systems gen_n2 ([T31]) and gen_n3 ([T22])  (round 7, verifyfl).
   The equations of a cell are the coefficients of R_i(sum_r x_r B_r) (keyed by the x-monomial) plus 'extra' polynomials.
   For a chain of x-index sets S_1 c S_2 c ... c S_last = all, stage S uses
        (coefficients whose x-monomial only involves x_r, r in S)  +  extra  +  GB of every earlier stage S' c S.
   Every polynomial used is in the ideal of the full cell, so the final ideal EQUALS the ideal of the cell: UNIT at the last stage
   <=> the cell is the unit ideal (mod p).
   usage: python3 -I subcut.py n2 P MSPEC CELL STAGE OUTPREFIX "0;0,1;0,2" [timeout]
          python3 -I subcut.py n3 P MSPEC CASEIDX SCELL OUTPREFIX "0,1;0,1,2;0,1,3" [Nfix=NAME] [timeout]"""
import exactlib as X
def msolve(fn, tmo):
    t0 = time.time()
    th = os.environ.get('MSOLVE_THREADS'); cmd = ['/usr/bin/msolve', '-g', '2'] + (['-t', th] if th else []) + ['-f', fn, '-o', fn + '.gb']
    subprocess.run(cmd, capture_output=True, timeout=tmo)
    s = open(fn + '.gb').read(); body = s[s.index('['):].strip().rstrip(':').strip()[1:-1]
    return [x.strip() for x in body.split(',\n') if x.strip()], time.time() - t0
def used_names(names, polys, gbtexts):
    import re
    ids = {v for q in polys for mon in q for v in mon}
    txt = ' '.join(gbtexts); out = []
    for i, n in enumerate(names):
        if i in ids or re.search(r'\b%s\b' % re.escape(n), txt): out.append(n)
    return out
def run(names, eqs, extra, p, stages, out, tmo, pre=()):
    gbs = [((), list(pre))] if pre else []
    for k, S in enumerate(stages):
        xs = {X.XOFF + r for r in S}
        polys = [e for (i, xm), e in eqs.items() if e and set(xm) <= xs] + list(extra)
        prev = [g for (S0, G) in gbs if set(S0) <= set(S) for g in G]
        fn = '%s_st%d.ms' % (out, k); vn = used_names(names, polys, prev)
        with open(fn, 'w') as f:
            f.write(','.join(vn) + '\n' + str(p) + '\n' + ',\n'.join([X.fmt_poly(q, names) for q in polys] + prev) + '\n')
        G, dt = msolve(fn, tmo)
        print('stage %d S=%s: %d polys + %d inherited, %d vars -> GB %d elements (%.1fs)%s' % (k, S, len(polys), len(prev), len(vn), len(G), dt, '  UNIT' if G == ['1'] else ''), flush=True)
        gbs.append((S, G))
        if G == ['1']: return 'UNIT'
    return 'NONUNIT'
def main():
    kind = sys.argv[1]; p = int(sys.argv[2]); mspec = sys.argv[3]; out = sys.argv[6]
    stages = [[int(x) for x in s.split(',')] for s in sys.argv[7].split(';')]
    opts = dict(a.split('=', 1) for a in sys.argv[8:] if '=' in a); tmo = float(opts.get('timeout', 1500))
    if kind == 'n2':
        import gen_n2
        names, eqs, extra = gen_n2.build(p, mspec, int(sys.argv[4]), sys.argv[5], keyed=True)
        desc = 'n2 cell %s stage %s' % (sys.argv[4], sys.argv[5])
    else:
        import gen_n3, gen_n1s
        nf = opts.get('Nfix'); ci = int(sys.argv[4]); case = None if nf else gen_n1s.cases(2)[ci]
        names, eqs, extra = gen_n3.build(p, mspec, case, int(sys.argv[5]), nf, keyed=True)
        desc = 'n3 case %s scell %s Nfix %s' % (case, sys.argv[5], nf)
    v = run(names, eqs, extra, p, stages, out, tmo)
    print('VERDICT %s m=%s p=%d: %s' % (desc, mspec, p, v), flush=True)
if __name__ == '__main__': main()
def run_deg(names, eqs, extra, p, degstages, out, tmo, pre=()):
    """stages given by maximal x-degrees per generator, e.g. (4,1,0): coefficients whose x-monomial has degree <= 4 in x_0, <= 1 in x_1,
    0 in x_2.  Stage T inherits the GB of every earlier stage T' <= T (componentwise).  All polynomials lie in the ideal of the cell."""
    gbs = [(None, list(pre))] if pre else []
    for k, T in enumerate(degstages):
        def ok(xm): return all(xm.count(X.XOFF + r) <= T[r] for r in range(len(T)))
        polys = [e for (i, xm), e in eqs.items() if e and ok(xm)] + list(extra)
        prev = [g for (T0, G) in gbs if T0 is None or all(a <= b for a, b in zip(T0, T)) for g in G]
        fn = '%s_d%d.ms' % (out, k); vn = used_names(names, polys, prev)
        with open(fn, 'w') as f:
            f.write(','.join(vn) + '\n' + str(p) + '\n' + ',\n'.join([X.fmt_poly(q, names) for q in polys] + prev) + '\n')
        try:
            G, dt = msolve(fn, tmo)
        except Exception as ex:
            print('stage %d T=%s: msolve FAILED (%s)' % (k, T, type(ex).__name__), flush=True); return 'FAIL'
        print('stage %d T=%s: %d polys + %d inherited, %d vars -> GB %d elements (%.1fs)%s' % (k, T, len(polys), len(prev), len(vn), len(G), dt, '  UNIT' if G == ['1'] else ''), flush=True)
        gbs.append((T, G))
        if G == ['1']: return 'UNIT'
    return 'NONUNIT'
