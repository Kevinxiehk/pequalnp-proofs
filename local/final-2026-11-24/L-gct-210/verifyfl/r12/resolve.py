import sys, os, re, ast, time; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact')
"""resolve.py (round 12): RE-SOLVE every UNIT line of a cover manifest with the CURRENT generator and the E-STALE-OUTPUT-guarded run_msolve
   (exactlib_fixed: old output removed first, returncode 0 and non-empty output required), in a fresh directory.  Prints a line per
   case and a summary; any verdict other than UNIT is reported as a MISMATCH.   usage: python3 -I resolve.py OUTDIR TIMEOUT MANIFEST [...]"""
import exactlib as X, exactlib_fixed, gen_n1s, gen_dc, gen_sym
pat = re.compile(r'^(\S+\.ms)(?: idx=(\d+))? case=(\(.*?\)) nvars=(\d+) npolys=(\d+) verdict=(\S+)')
od, tmo = sys.argv[1], float(sys.argv[2]); os.makedirs(od, exist_ok=True)
for man in sys.argv[3:]:
    base = os.path.basename(man); mm = re.match(r'^(n1s|dc|sym)_?(.*?)_p(\d+)_k(\d+)\.manifest$', base)
    kind, spec, p = mm.group(1), mm.group(2), int(mm.group(3)); st = {}; bad = []; t0 = time.time()
    for line in open(man):
        q = pat.match(line)
        if not q or not q.group(6).startswith('UNIT'): continue
        fn, case = q.group(1), ast.literal_eval(q.group(3))
        if kind == 'n1s': names, polys = gen_n1s.build(p, spec, case)
        elif kind == 'dc': names, polys = gen_dc.build(p, spec, case)
        else: names, polys = gen_sym.build(p, spec, case)
        if X.trivially_unit(polys): v = 'UNIT'
        else:
            path = os.path.join(od, fn); X.write_msolve(path, names, p, polys)
            v, nb, dt = exactlib_fixed.run_msolve(path, timeout=tmo)
            if v == 'UNIT': os.remove(path); os.remove(path + '.gb')
        st[v] = st.get(v, 0) + 1
        if v != 'UNIT': bad.append('%s %s -> %s' % (fn, case, v))
    print('%s: re-solved %s  (%.0fs)%s' % (man, st, time.time() - t0, ''.join('\n  MISMATCH ' + b for b in bad)), flush=True)
