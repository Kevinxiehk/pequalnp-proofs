import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
"""gen_dc.py -- [DC-k] STRUCTURED for ANY defect line m (|supp m| = 2..5)  (round 7, verifyfl; generalises gen_n1s.py).
   P = supp m (sorted), Nt = neutral columns (m_n = 0).  By (F2) [valid in char p > 3, NOTES-verifyfl R7.1] on a doubly centred space N
   with defect in C m every neutral column lies on an isotropic line C v_n (or vanishes).  N is described by
     rho  = rank of nu : N -> C^Nt, Z -> (lam_n)_n  (column n = lam_n v_n);  its image = reduced-echelon cell of Gr(rho, |Nt|);
     N_P  = ker nu = (k - rho)-dim subspace of dcsub(P) (doubly centred, supported on P; dim 3(|P|-1)), reduced-echelon cell;
     rho complement elements: nu-values = the echelon rows of the image cell; P-coordinates free except at the pivots of N_P (= 0);
          neutral column n gets lam_n v_n, and the LAST column of P gets -lam_n v_n (row sums stay 0).
   vtypes per neutral column: 'ab' (v = (1,a,b,-1-a-b), quadric), 'z1' = (0,1,w,w^2), 'z2' = (0,1,w^2,w)  (all isotropic lines, char != 2,3).
   For Nt = {3,4} this is EXACTLY gen_n1s.py (checked by test_gen_dc.py: identical equation sets in all cases).
   usage: python3 -I gen_dc.py P MSPEC K OUTDIR [run] [timeout=T] [first last] [resume]   (resume: skip idx already in the manifest)"""
import exactlib as X, itertools, time
VT = ('ab', 'z1', 'z2')
def setup(p, mspec):
    """'SL', 'SL4', 'SL5' = strongly level (all C_j = 24; every column is neutral, so ANY split P/Nt is valid): calibrations with
    the column split of the supports 3, 4, 5 respectively."""
    cs = X.Consts(p)
    if mspec.startswith('C:'):
        # defect SPACE C = span of the listed vectors (e = dim C), e.g. 'C:1,2,-3,0,0;0,1,1,-2,0'; W = basis of C^perp (rank 5 - e);
        # P = union of the supports, Nt = columns where every vector of C vanishes ((F2)_p holds for those columns, NOTES R8.6)
        vecs = [[cs.tok(t) for t in v.split(',')] for v in mspec[2:].split(';')]
        for v in vecs: assert len(v) == 5 and sum(v) % p == 0
        rows, piv = X.rref(vecs, p); e = len(piv)
        free = [c for c in range(5) if c not in piv]; W = []
        for f in free:
            w = [0] * 5; w[f] = 1
            for r, pc in enumerate(piv): w[pc] = (-rows[r][f]) % p
            W.append(w)
        for w in W:
            for v in vecs: assert sum(a * b for a, b in zip(w, v)) % p == 0
        P = [j for j in range(5) if any(v[j] for v in vecs)]; Nt = [j for j in range(5) if j not in P]
        return cs, vecs, W, P, Nt
    if mspec.startswith('SL'):
        m, W = X.parse_m('SL', cs); np_ = {'SL': 3, 'SL4': 4, 'SL5': 5}[mspec]
        return cs, m, W, list(range(np_)), list(range(np_, 5))
    m, W = X.parse_m(mspec, cs)
    P = [j for j in range(5) if m[j]]; Nt = [j for j in range(5) if not m[j]]
    return cs, m, W, P, Nt
def cases(k, P, Nt):
    out = []; nP = 3 * (len(P) - 1)
    for rho in range(min(len(Nt), k), -1, -1):
        if k - rho > nP: continue
        for piv in X.cells(nP, k - rho):
            for img in X.cells(len(Nt), rho):              # pivot columns of the image cell (indices into Nt)
                # neutral columns that can be active: those at or after the first pivot... every column after a pivot can be nonzero
                act = sorted({t for t in range(len(Nt)) if rho and t >= img[0]})
                for vts in itertools.product(VT, repeat=len(act)):
                    out.append((k, rho, piv, img, tuple(zip(act, vts))))
    return out
def build(p, mspec, case, keyed=False):
    cs, m, W, P, Nt = setup(p, mspec); V = X.Vars()
    B, extra, ells = basis(p, cs, P, Nt, case, V)
    if keyed: return V.names, X.equations(B, W, p, keyed=True), extra, B
    polys, nx = X.equations(B, W, p)
    return V.names, polys + extra
def basis(p, cs, P, Nt, case, V):
    """generators of N for a case (same construction as always), the chart quadrics, and gauge forms 'ells' (lists of entries
    (row, col) whose sum is a linear form) with [ell_i(B_j)] = identity: pivot P-coordinates of N_P, then for each complement element
    the entry (vrow, neutral column of its image pivot), vrow = 0 for chart 'ab', 1 for 'z1'/'z2'."""
    k, rho, piv, img, acts = case
    rows = X.echelon_rows(3 * (len(P) - 1), piv, V, 'u') if k - rho > 0 else []
    B = [X.dcsub_matrix(r, P, p) for r in rows]
    vec = {}; extra = []
    for t, vt in acts:
        nm = str(Nt[t])
        if vt == 'ab':
            a = V.new('a' + nm); b = V.new('b' + nm); last = X.padd(X.padd(X.pconst(-1, p), a, p, -1), b, p, -1)
            vec[t] = [X.pconst(1, p), a, b, last]; q = X.pconst(1, p)
            for c in (a, b, last): q = X.padd(q, X.pmul(c, c, p), p)
            extra.append(q)
        elif vt == 'z1': vec[t] = [X.pconst(c, p) for c in (0, 1, cs.w, cs.w * cs.w % p)]
        else: vec[t] = [X.pconst(c, p) for c in (0, 1, cs.w * cs.w % p, cs.w)]
    # image cell rows: row r has 1 at img[r], 0 at the other pivots and before img[r], unknown 'al' entries elsewhere
    nus = []
    for r, pr in enumerate(img):
        row = {}
        for t in range(len(Nt)):
            if t == pr: row[t] = {(): 1}
            elif t in img or t < pr: row[t] = {}
            else: row[t] = V.new('al' if len(Nt) == 2 else 'al%d_%d' % (r, t))
        nus.append(row)
    last = P[-1]
    for r, row in enumerate(nus):
        co = [({} if d in piv else V.new('y%d_%d' % (r, d))) for d in range(3 * (len(P) - 1))]
        M = X.dcsub_matrix(co, P, p)
        for t in range(len(Nt)):
            lam = row[t]
            if lam and t in vec:
                for a in range(4):
                    e = X.pmul(lam, vec[t][a], p); M[a][Nt[t]] = X.padd(M[a][Nt[t]], e, p); M[a][last] = X.padd(M[a][last], e, p, -1)
        B.append(M)
    vrow = {t: (0 if vt == 'ab' else 1) for t, vt in acts}
    ells = [[(d % 3, P[d // 3])] for d in piv] + [[(vrow[pr], Nt[pr])] for pr in img]
    return B, extra, ells
def casename(c):
    k, rho, piv, img, acts = c
    return 'k%d_rho%d_piv%s_img%s_%s' % (k, rho, ''.join('%x' % d for d in piv) or 'none', ''.join(map(str, img)) or 'none', '_'.join('%d%s' % a for a in acts) or 'x')
def main():
    p = int(sys.argv[1]); mspec = sys.argv[2]; k = int(sys.argv[3]); outdir = sys.argv[4]
    opts = dict(a.split('=') for a in sys.argv if '=' in a); run = 'run' in sys.argv; tmo = float(opts.get('timeout', 60))
    cs, m, W, P, Nt = setup(p, mspec); cl = cases(k, P, Nt)
    nums = [a for a in sys.argv[5:] if a.isdigit()]
    first = int(nums[0]) if len(nums) == 2 else 0; last = int(nums[1]) if len(nums) == 2 else len(cl)
    os.makedirs(outdir, exist_ok=True); tag = 'dc_%s_p%d' % (mspec.replace(',', '_'), p)
    mpath = os.path.join(outdir, tag + '_k%d.manifest' % k); done = set()
    if 'resume' in sys.argv and os.path.exists(mpath):        # skip every idx that already has a verdict line in the manifest
        import re
        for line in open(mpath):
            mm = re.search(r' idx=(\d+) ', line)
            if mm and 'verdict=' in line: done.add(int(mm.group(1)))
    man = open(mpath, 'a'); t0 = time.time(); stats = {}
    for idx in range(first, min(last, len(cl))):
        if idx in done: continue
        names, polys = build(p, mspec, cl[idx]); fn = os.path.join(outdir, '%s_%s.ms' % (tag, casename(cl[idx])))
        if not polys: verdict = 'NONUNIT(no-equations)'; extra = ''
        elif X.trivially_unit(polys): verdict = 'UNIT(constant-equation)'; extra = ''
        else:
            X.write_msolve(fn, names, p, polys); verdict = 'not-run'; extra = ''
            if run:
                v, nb, dt = X.run_msolve(fn, timeout=tmo); verdict = v; extra = ' basis=%s time=%.2fs' % (nb, dt)
                if v == 'UNIT':
                    os.remove(fn)
                    if os.path.exists(fn + '.gb'): os.remove(fn + '.gb')
        stats[verdict] = stats.get(verdict, 0) + 1
        man.write('%s idx=%d case=%s nvars=%d npolys=%d verdict=%s%s\n' % (os.path.basename(fn), idx, cl[idx], len(names), len(polys), verdict, extra)); man.flush()
    print('%s k=%d cases %d..%d of %d: %s  (%.0fs)' % (tag, k, first, min(last, len(cl)) - 1, len(cl), stats, time.time() - t0))
if __name__ == '__main__': main()
