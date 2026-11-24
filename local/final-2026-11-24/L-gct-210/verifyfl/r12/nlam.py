import sys, subprocess, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
"""nlam.py -- N-systems of piece-IV / P-pieces with the JUNK REMOVAL lambda-charts (R17.4) and the early two-column Rabinowitsch (R16.2),
   optionally + the permanent relations (R14.4/R14.5; valid since every lam_k is nonzero on N in these charts).  N-level UNIT for all 8 words
   decides the item.  usage: python3 -I nlam.py C CI NB NBARGS [perm] [mu] [TMO]   (mu: the P-piece junk removal R17.5 instead of the lambda-words)"""
import exactlib as X, gen_t22rad as G, gen_n1s, gen_sym, gen_sym_n3
p = 2147483629; chart, ci, nb, nba = sys.argv[1], int(sys.argv[2]), sys.argv[3], (None if sys.argv[4] == '-' else sys.argv[4])
perm = 'perm' in sys.argv[5:]; MU = 'mu' in sys.argv[5:]; MUP = 'muperm' in sys.argv[5:]; P2R = [a[3:] for a in sys.argv[5:] if a.startswith('p2=')]; P2R = P2R[0] if P2R else None; ALS = [a[3:] for a in sys.argv[5:] if a.startswith('al=')]; ALS = ALS[0] if ALS else None; tmo = [a for a in sys.argv[5:] if a.isdigit()]; tmo = tmo[0] if tmo else '120'
res = {}
WORDS = ('AAA', 'AAB', 'ABA', 'ABB', 'BAA', 'BAB', 'BBA', 'BBB') if not MU else ('mu',)
if nb == 't0b' and not MU:                       # columns with u_k = '0' carry no lam_k: keep only letter 'A' there (no duplicate words)
    uks_ = nba.split(':'); WORDS = tuple(w for w in WORDS if all(w[k] == 'A' or uks_[k] != '0' for k in range(3)))
for word in WORDS:
    # build the full Y-free system through gen_t22rad.build (scell-free part): use rc = 6 and keep only the N-equations + N-extras
    nm, eqs, extra = G.build(p, chart, ci, nb, nba, 6, keyed=True, rab=True, lamch=(None if MU else word), mu=MU, muperm=MUP, p2rank=P2R, alsplit=ALS, perm34=perm, permP=perm)
    yv = {i for i, n in enumerate(nm) if n.startswith('w') or n.startswith('r')}
    polys = [e for (i, xm), e in eqs.items() if e and set(xm) <= {X.XOFF, X.XOFF + 1}] + [q for q in extra if q and not any(v in yv for mon in q for v in mon)]
    ids = sorted({v for q in polys for mon in q for v in mon}); names = [nm[i] for i in ids]
    tag = '%s_%s_c%d_%s' % (nb, chart, ci, (nba or '-').replace('/', '_').replace(':', ''))
    fn = '/home/kevxhk/work/L-gct-210/verifyfl/r12/nlam/%s_%s%s%s.ms' % (tag, word, 'P' if perm else '', P2R or '')
    os.makedirs(os.path.dirname(fn), exist_ok=True)
    if X.trivially_unit(polys): v = 'UNIT(const)'
    else:
        with open(fn, 'w') as f: f.write(','.join(names) + '\n' + str(p) + '\n' + ',\n'.join(X.fmt_poly(q, nm) for q in polys) + '\n')
        if os.path.exists(fn + '.gb'): os.remove(fn + '.gb')
        r = subprocess.run(['python3', '-I', '/home/kevxhk/work/L-gct-210/verifyfl/r12/rsscap.py', os.environ.get('NLAM_CAP', '550'), tmo, '/usr/bin/msolve', '-g', '2', '-t', '1', '-f', fn, '-o', fn + '.gb'], capture_output=True, text=True)
        b = open(fn + '.gb').read() if os.path.exists(fn + '.gb') else ''
        v = ('FAIL(cap/timeout)' if 'RSSCAP' in r.stdout else 'FAIL(rc%d)' % r.returncode) if (r.returncode or not b) else ('UNIT' if b[b.index('['):].strip().rstrip(':').strip()[1:-1].strip() == '1' else 'NONUNIT')
    res[word] = v; print('  %s %s word %s%s: %s' % (nb, nba, word, ' +perm' if perm else '', v), flush=True)
print('VERDICT nlam %s c%d %s %s%s%s: %s' % (chart, ci, nb, nba, ' +perm' if perm else '', ((' p2=' + P2R) if P2R else '') + ((' al=' + ALS) if ALS else ''), 'N-UNIT in all words' if all(v.startswith('UNIT') for v in res.values()) else res), flush=True)
