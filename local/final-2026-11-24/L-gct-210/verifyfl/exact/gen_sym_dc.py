import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
"""gen_sym_dc.py -- SYM-M for [DC-k], ANY support size s = |P| (P = columns 0..s-1), m a POINT OF P(W_P) (round 11, verifyfl; NOTES R11.2).
   W_P = zero-sum vectors on P (dim s-1), P(W_P) = P^{s-2}.  Chart c (c in P minus the last column): m_c = 1, the other m_j (j in P,
   j != c, j != last) are parameters mp_j, m_last = -(1 + sum).  Basis of m^perp, polynomial and of rank 4 at EVERY point of the chart:
   {e_n : n neutral} + {e_j - m_j e_c : j in P, j != c}.  The charts c = 0..s-2 cover P(W_P) (m_c = 0 for all c < s-1 forces m = 0).
   The structured cover of gen_dc (k-dim doubly centred spaces; (F2) used only on the neutral columns) is valid at every point.  By
   properness of Gr(k, D) x P^{s-2}: UNIT in F_p[params, x] in every chart => empty for every m with supp m c P, in char 0 (R10.8).
   usage: python3 -I gen_sym_dc.py P S CHART K OUTDIR [first last] [run] [timeout=T] [resume]"""
import exactlib as X, gen_dc, gen_sym, itertools, time, re
def setup(s):
    P = list(range(s)); Nt = list(range(s, 5)); return P, Nt
def wpoly(p, s, c, V):
    P, Nt = setup(s); one = X.pconst(1, p)
    m = {}
    free = [j for j in P if j != c and j != P[-1]]
    for j in free: m[j] = V.new('mp%d' % j)
    m[c] = one
    tot = X.padd(one, {}, p)
    for j in free: tot = X.padd(tot, m[j], p)
    m[P[-1]] = X.pmul(X.pconst(p - 1, p), tot, p)
    W = [[one if a == n else {} for a in range(5)] for n in Nt]
    for j in P:
        if j == c: continue
        row = [{} for _ in range(5)]; row[j] = one; row[c] = X.pmul(X.pconst(p - 1, p), m[j], p); W.append(row)
    assert len(W) == 4
    return W, m
def build(p, s, c, case, keyed=False):
    cs = X.Consts(p); V = X.Vars(); P, Nt = setup(s)
    Wp, m = wpoly(p, s, c, V)
    B, extra, ells = gen_dc.basis(p, cs, P, Nt, case, V)
    if keyed: return V.names, gen_sym.equations_poly(B, Wp, p, keyed=True), extra, B
    return V.names, gen_sym.equations_poly(B, Wp, p) + extra
def main():
    p = int(sys.argv[1]); s = int(sys.argv[2]); c = int(sys.argv[3]); k = int(sys.argv[4]); outdir = sys.argv[5]
    P, Nt = setup(s); cl = gen_dc.cases(k, P, Nt)
    opts = dict(a.split('=') for a in sys.argv if '=' in a); run = 'run' in sys.argv; tmo = float(opts.get('timeout', 60))
    nums = [a for a in sys.argv[6:] if a.isdigit()]
    first = int(nums[0]) if len(nums) == 2 else 0; last = int(nums[1]) if len(nums) == 2 else len(cl)
    os.makedirs(outdir, exist_ok=True); tag = 'symdc_s%d_c%d_p%d' % (s, c, p)
    mpath = os.path.join(outdir, tag + '_k%d.manifest' % k); done = set()
    if 'resume' in sys.argv and os.path.exists(mpath):
        for line in open(mpath):
            mm = re.search(r' idx=(\d+) ', line)
            if mm and 'verdict=' in line: done.add(int(mm.group(1)))
    man = open(mpath, 'a'); t0 = time.time(); stats = {}
    for idx in range(first, min(last, len(cl))):
        if idx in done: continue
        names, polys = build(p, s, c, cl[idx]); fn = os.path.join(outdir, '%s_%s.ms' % (tag, gen_dc.casename(cl[idx])))
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
