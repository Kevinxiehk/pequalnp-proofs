import sys, os, re, subprocess, time; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact')
"""cut_cell.py -- decide one generic rank-2 cell of [DC3] (gen_n1s case (3,2,(PIV,),0,T3,T4)) by the SUBSYSTEM CUT:
   S1 = coefficients of R_i(x_0 Z_0 + x_1 Z_1) (+ isotropy quadric of v_3), S2 = same with Z_2 (+ quadric of v_4).
   GB(S1), GB(S2) lie in the ideal of the cell, so  ideal(FULL) = ideal(FULL + GB(S1) + GB(S2)).
   If T3 == T4, S2 is S1 with (a3,b3,y0_*) -> (a4,b4,y1_*) renamed (CHECKED: equal as sets up to scalars), so GB(S2) = renamed GB(S1)
   (reduced GBs are unique and the renaming preserves the positions in the variable order).  Otherwise GB(S2) is computed.
   FULL is asserted identical to gen_n1s.build(case).   usage: python3 -I cut_cell.py P MSPEC PIV T3 T4 OUTPREFIX [timeout]"""
import exactlib as X, gen_n1s
p = int(sys.argv[1]); mspec = sys.argv[2]; piv = int(sys.argv[3]); t3, t4 = sys.argv[4], sys.argv[5]; out = sys.argv[6]
tmo = float(sys.argv[7]) if len(sys.argv) > 7 else 1200
case = (3, 2, (piv,), 0, t3, t4)
cs = X.Consts(p); m, W = X.parse_m(mspec, cs); V = X.Vars()
rows = X.echelon_rows(6, (piv,), V, 'u'); B = [X.dcsub_matrix(r, [0, 1, 2], p) for r in rows]
vec = {}; extra = {}
for name, t in (('3', t3), ('4', t4)):
    if t == 'ab':
        a = V.new('a' + name); b = V.new('b' + name); last = X.padd(X.padd(X.pconst(-1, p), a, p, -1), b, p, -1)
        vec[name] = [X.pconst(1, p), a, b, last]; q = X.pconst(1, p)
        for c in (a, b, last): q = X.padd(q, X.pmul(c, c, p), p)
        extra[name] = q
    elif t == 'z1': vec[name] = [X.pconst(c, p) for c in (0, 1, cs.w, cs.w * cs.w % p)]
    elif t == 'z2': vec[name] = [X.pconst(c, p) for c in (0, 1, cs.w * cs.w % p, cs.w)]
for r, (l3, l4) in enumerate([({(): 1}, {}), ({}, {(): 1})]):
    co = [({} if d == piv else V.new('y%d_%d' % (r, d))) for d in range(6)]
    M = X.dcsub_matrix(co, [0, 1, 2], p)
    for lam, name, col in ((l3, '3', 3), (l4, '4', 4)):
        if lam:
            for a in range(4):
                e = X.pmul(lam, vec[name][a], p); M[a][col] = X.padd(M[a][col], e, p); M[a][2] = X.padd(M[a][2], e, p, -1)
    B.append(M)
eqs = X.equations(B, W, p, keyed=True)
full = [e for e in eqs.values() if e] + list(extra.values())
names0, polys0 = gen_n1s.build(p, mspec, case)
assert names0 == V.names and sorted(sorted(q.items()) for q in polys0) == sorted(sorted(q.items()) for q in full), 'mismatch with gen_n1s'
x1, x2 = X.XOFF + 1, X.XOFF + 2
S = {'S1': [e for (i, xm), e in eqs.items() if e and x2 not in xm] + ([extra['3']] if '3' in extra else []),
     'S2': [e for (i, xm), e in eqs.items() if e and x1 not in xm] + ([extra['4']] if '4' in extra else [])}
def canon(q):
    lead = max(q); iv = X.inv(q[lead], p); return frozenset((k, v * iv % p) for k, v in q.items())
def write_used(fn, polys):
    ids = sorted({v for q in polys for mon in q for v in mon}); names = V.names
    with open(fn, 'w') as f:
        f.write(','.join(names[i] for i in ids) + '\n' + str(p) + '\n' + ',\n'.join(X.fmt_poly(q, names) for q in polys) + '\n')
def msolve(fn):
    t0 = time.time()
    subprocess.run(['/usr/bin/msolve', '-g', '2', '-f', fn, '-o', fn + '.gb'], capture_output=True, timeout=tmo)
    s = open(fn + '.gb').read(); body = s[s.index('['):].strip().rstrip(':').strip()[1:-1]
    return [x.strip() for x in body.split(',\n') if x.strip()], time.time() - t0
X.write_msolve(out + '_FULL.ms', V.names, p, full)
write_used(out + '_S1.ms', S['S1']); g1, dt1 = msolve(out + '_S1.ms'); print('GB(S1): %d elements, %.1fs' % (len(g1), dt1), flush=True)
if t3 == t4:
    ren = {V.names.index('a3'): V.names.index('a4'), V.names.index('b3'): V.names.index('b4')} if t3 == 'ab' else {}
    for d in range(6):
        if d != piv: ren[V.names.index('y0_%d' % d)] = V.names.index('y1_%d' % d)
    def rn(q): return {tuple(sorted(ren.get(v, v) for v in mon)): c for mon, c in q.items()}
    assert set(canon(rn(q)) for q in S['S1']) == set(canon(q) for q in S['S2']), 'S2 is not the renamed S1'
    nm = {V.names[a]: V.names[b] for a, b in ren.items()}
    pat = re.compile(r'\b(' + '|'.join(map(re.escape, nm)) + r')\b')
    g2 = [pat.sub(lambda mm: nm[mm.group(1)], x) for x in g1]; print('S2 = renamed S1 (checked); GB(S2) by renaming', flush=True)
else:
    write_used(out + '_S2.ms', S['S2']); g2, dt2 = msolve(out + '_S2.ms'); print('GB(S2): %d elements, %.1fs' % (len(g2), dt2), flush=True)
with open(out + '_FULLGB.ms', 'w') as f:
    f.write(','.join(V.names) + '\n' + str(p) + '\n' + ',\n'.join([X.fmt_poly(q, V.names) for q in full] + g1 + g2) + '\n')
g, dt = msolve(out + '_FULLGB.ms')
print('VERDICT case=%s m=%s p=%d: %s (FULL+GB: %d elements, %.1fs)' % (case, mspec, p, 'UNIT' if g == ['1'] else 'NONUNIT', len(g), dt), flush=True)
