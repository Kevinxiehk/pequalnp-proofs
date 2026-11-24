import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
"""gen_sym.py -- SYM-M: [DC3] with the defect line as a PARAMETER on the projective line of lines supported on columns 0, 1, 2 (round 10).
   chart A: m = (1, t, -1-t, 0, 0), W = {e_3, e_4, (-t, 1, 0, 0, 0), (1+t, 0, 1, 0, 0)};
   chart B: m = (t, 1, -1-t, 0, 0), W = {e_3, e_4, (1, -t, 0, 0, 0), (0, 1+t, 1, 0, 0)}  (rank 4 for every t; A and B cover P(W_P)).
   The structured cover of gen_n1s (k-dim doubly centred spaces; (F2) uses only the neutral columns 3, 4) is valid for EVERY m on this line.
   KEY POINT (NOTES R10.8): the family {(N, m)} is closed in Gr(k, D) x P^1, hence proper; so if a case is the UNIT ideal in F_p[t, x] in
   BOTH charts, then no m on the line (in characteristic 0) admits a solution of that case.  Non-unit cases need the elimination ideal in t.
   usage: python3 -I gen_sym.py P CHART K OUTDIR [first last] [run] [timeout=T]"""
import exactlib as X, gen_n1s, itertools, time
def equations_poly(B, Wp, p, keyed=False):
    """as exactlib.equations, but W has POLYNOMIAL entries (dicts)"""
    k = len(B); E = [[{} for _ in range(5)] for _ in range(4)]
    for r in range(k):
        xr = (X.XOFF + r,)
        for a in range(4):
            for c in range(5):
                for mon, v in B[r][a][c].items(): E[a][c][mon + xr] = v
    C = []
    for j in range(5):
        cols = [c for c in range(5) if c != j]; tot = {}
        for d in (1, 2, 3, 4):
            f = X.FACT[4 - d]
            for rows in itertools.combinations(range(4), d):
                for cs_ in itertools.combinations(cols, d):
                    for perm in itertools.permutations(cs_):
                        fac = [E[rows[t]][perm[t]] for t in range(d)]
                        if any(not q for q in fac): continue
                        pr = fac[0]
                        for q in fac[1:]: pr = X.pmul(pr, q, p)
                        for mon, v in pr.items():
                            x = (tot.get(mon, 0) + f * v) % p
                            if x: tot[mon] = x
                            elif mon in tot: del tot[mon]
        C.append(tot)
    eqs = {}
    for i, wr in enumerate(Wp):
        for j in range(5):
            if not wr[j]: continue
            for mon, v in C[j].items():
                cut = len(mon)
                while cut > 0 and mon[cut - 1] >= X.XOFF: cut -= 1
                key = (i, mon[cut:]); u = mon[:cut]
                eqs[key] = X.padd(eqs.get(key, {}), X.pmul(wr[j], {u: v}, p), p)
    if keyed: return eqs
    return [e for e in eqs.values() if e]
def build(p, chart, case, keyed=False):
    """same parametrisation as gen_n1s.build (copied), with the extra variable mt (first) and the t-dependent W."""
    k, rho, piv, lc, t3, t4 = case
    cs = X.Consts(p); V = X.Vars(); t = V.new('mt'); one = X.pconst(1, p)
    e = lambda j: [one if a == j else {} for a in range(5)]
    if chart == 'A': Wp = [e(3), e(4), [X.pmul(X.pconst(p - 1, p), t, p), one, {}, {}, {}], [X.padd(one, t, p), {}, one, {}, {}]]
    else: Wp = [e(3), e(4), [one, X.pmul(X.pconst(p - 1, p), t, p), {}, {}, {}], [{}, X.padd(one, t, p), one, {}, {}]]
    rows = X.echelon_rows(6, piv, V, 'u') if k - rho > 0 else []
    B = [X.dcsub_matrix(r, [0, 1, 2], p) for r in rows]
    vec = {}; extra = []
    for name, tt in (('3', t3), ('4', t4)):
        if tt == 'ab':
            a = V.new('a' + name); b = V.new('b' + name); last = X.padd(X.padd(X.pconst(-1, p), a, p, -1), b, p, -1)
            vec[name] = [one, a, b, last]; q = X.pconst(1, p)
            for c in (a, b, last): q = X.padd(q, X.pmul(c, c, p), p)
            extra.append(q)
        elif tt == 'z1': vec[name] = [X.pconst(c, p) for c in (0, 1, cs.w, cs.w * cs.w % p)]
        elif tt == 'z2': vec[name] = [X.pconst(c, p) for c in (0, 1, cs.w * cs.w % p, cs.w)]
        else: vec[name] = None
    if rho == 2: nus = [({(): 1}, {}), ({}, {(): 1})]
    elif rho == 1: nus = [({(): 1}, V.new('al'))] if lc == 0 else [({}, {(): 1})]
    else: nus = []
    for r, (l3, l4) in enumerate(nus):
        co = [({} if d in piv else V.new('y%d_%d' % (r, d))) for d in range(6)]
        M = X.dcsub_matrix(co, [0, 1, 2], p)
        for lam, name, col in ((l3, '3', 3), (l4, '4', 4)):
            if lam and vec[name] is not None:
                for a in range(4):
                    ee = X.pmul(lam, vec[name][a], p); M[a][col] = X.padd(M[a][col], ee, p); M[a][2] = X.padd(M[a][2], ee, p, -1)
        B.append(M)
    if keyed: return V.names, equations_poly(B, Wp, p, keyed=True), extra
    return V.names, equations_poly(B, Wp, p) + extra
def main():
    p = int(sys.argv[1]); chart = sys.argv[2]; k = int(sys.argv[3]); outdir = sys.argv[4]; cl = gen_n1s.cases(k)
    opts = dict(a.split('=') for a in sys.argv if '=' in a); run = 'run' in sys.argv; tmo = float(opts.get('timeout', 60))
    nums = [a for a in sys.argv[5:] if a.isdigit()]
    first = int(nums[0]) if len(nums) == 2 else 0; last = int(nums[1]) if len(nums) == 2 else len(cl)
    os.makedirs(outdir, exist_ok=True); tag = 'sym%s_p%d' % (chart, p)
    man = open(os.path.join(outdir, tag + '_k%d.manifest' % k), 'a'); t0 = time.time(); stats = {}
    for idx in range(first, min(last, len(cl))):
        names, polys = build(p, chart, cl[idx]); fn = os.path.join(outdir, '%s_%s.ms' % (tag, gen_n1s.casename(cl[idx])))
        if X.trivially_unit(polys): verdict = 'UNIT(constant-equation)'; extra = ''
        else:
            X.write_msolve(fn, names, p, polys); verdict = 'not-run'; extra = ''
            if run:
                v, nb, dt = X.run_msolve(fn, timeout=tmo); verdict = v; extra = ' basis=%s time=%.2fs' % (nb, dt)
                if v == 'UNIT':
                    os.remove(fn)
                    if os.path.exists(fn + '.gb'): os.remove(fn + '.gb')
        stats[verdict] = stats.get(verdict, 0) + 1
        man.write('%s idx=%d case=%s nvars=%d npolys=%d verdict=%s%s\n' % (os.path.basename(fn), idx, cl[idx], len(names), len(polys), verdict, extra)); man.flush()
    print('%s k=%d cases %d..%d: %s (%.0fs)' % (tag, k, first, min(last, len(cl)) - 1, stats, time.time() - t0))
if __name__ == '__main__': main()
