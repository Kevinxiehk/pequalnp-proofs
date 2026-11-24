import sys, os, re, ast, hashlib, tempfile; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact')
"""manifest_check.py (round 12, coordinator request after E-STALE-OUTPUT): for every line of a cover manifest, regenerate the system
   with the CURRENT generator (no solving) and compare (a) the file name (case naming), (b) nvars, npolys, and (c) if the original .ms
   is still on disk (non-UNIT cases), the sha256 of the msolve input text.  Also prints the sha256 of every regenerated system so that
   a later run can be compared.   usage: python3 -I manifest_check.py MANIFEST [MANIFEST ...]"""
import exactlib as X, gen_n1s, gen_dc, gen_sym
pat = re.compile(r'^(\S+\.ms)(?: idx=(\d+))? case=(\(.*?\)) nvars=(\d+) npolys=(\d+) verdict=(\S+)')
def text(names, p, polys):
    nm = names or ['dummy']
    return ','.join(nm) + '\n' + str(p) + '\n' + ',\n'.join(X.fmt_poly(q, nm) for q in polys) + '\n'
for man in sys.argv[1:]:
    base = os.path.basename(man); d = os.path.dirname(man)
    mm = re.match(r'^(n1s|dc|sym)_?(.*?)_p(\d+)_k(\d+)\.manifest$', base)
    kind, spec, p, k = mm.group(1), mm.group(2), int(mm.group(3)), int(mm.group(4))
    if kind == 'sym': chart = spec
    cache = {}; n = bad = hashed = hashbad = 0; seen = {}; report = []
    for line in open(man):
        q = pat.match(line)
        if not q: report.append('  unparsed: ' + line.strip()); continue
        fn, idx, case, nv, npl, verdict = q.group(1), q.group(2), ast.literal_eval(q.group(3)), int(q.group(4)), int(q.group(5)), q.group(6)
        n += 1
        if case not in cache:
            if kind == 'n1s': names, polys = gen_n1s.build(p, spec, case); exp = 'n1s_%s_p%d_%s.ms' % (spec, p, gen_n1s.casename(case))
            elif kind == 'dc': names, polys = gen_dc.build(p, spec, case); exp = 'dc_%s_p%d_%s.ms' % (spec, p, gen_dc.casename(case))
            else: names, polys = gen_sym.build(p, chart, case); exp = 'sym%s_p%d_%s.ms' % (chart, p, gen_n1s.casename(case))
            txt = text(names, p, polys); cache[case] = (len(names), len(polys), hashlib.sha256(txt.encode()).hexdigest(), exp)
        nv2, np2, h2, exp = cache[case]
        msg = []
        if fn != exp: msg.append('name %s != %s' % (fn, exp))
        if (nv, npl) != (nv2, np2): msg.append('nvars/npolys manifest %d/%d, now %d/%d' % (nv, npl, nv2, np2))
        orig = os.path.join(d, fn)
        if os.path.exists(orig):
            hashed += 1; h1 = hashlib.sha256(open(orig, 'rb').read()).hexdigest()
            if h1 != h2: msg.append('sha256 of the .ms on disk differs from the regenerated system'); hashbad += 1
        if idx is not None:
            seen.setdefault(int(idx), []).append(verdict)
        if msg: bad += 1; report.append('  CHANGED idx=%s case=%s verdict=%s: %s' % (idx, case, verdict, '; '.join(msg)))
    dup = {i: v for i, v in seen.items() if len(v) > 1}
    print('%s: %d lines, %d distinct cases, %d changed, %d .ms on disk hashed (%d differ), %d idx with >1 line %s' % (man, n, len(cache), bad, hashed, hashbad, len(dup), dup if dup else ''))
    for r in report[:30]: print(r)
    sys.stdout.flush()
