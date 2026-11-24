import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
"""gen_n1.py -- [DC-k]: k-dimensional spaces of DOUBLY CENTRED 4x5 matrices (all row and column sums 0) with defect in C m.
   mode 'dc'  : ambient D (dim 12), basis (e_a - e_3)(e_q - e_4)^T, a < 3, q < 4; coordinate 4a+q = entry (a,q).
   mode '3col': ambient = matrices with zero column sums supported on the columns 0,1,2 (dim 9), coordinate 3q+a = entry (a,q)
                (cross-check of Lemma 3C: k = 4 must be UNIT in every cell, k = 3 is non-unit in some cells).
   One msolve file per reduced-echelon cell of Gr(k, n): unknowns = the free entries of the echelon matrix.
   usage: python3 -I gen_n1.py P MSPEC K MODE OUTDIR [first last] [run]     (cells first..last-1; 'run' = also call msolve)
   MSPEC: preset name (see exactlib.PRESETS), 'SL' (strongly level), or five comma separated entries (integers, w, w2, i, -i)."""
import exactlib as X, time, os
def build(p, mspec, k, mode, piv):
    cs = X.Consts(p); m, W = X.parse_m(mspec, cs); V = X.Vars(); n = 12 if mode == 'dc' else 9
    rows = X.echelon_rows(n, piv, V, 'u')
    B = [X.dc_matrix(r, p) if mode == 'dc' else X.col_matrix(r, [0, 1, 2], p) for r in rows]
    polys, nx = X.equations(B, W, p)
    return V.names, polys
def main():
    p = int(sys.argv[1]); mspec = sys.argv[2]; k = int(sys.argv[3]); mode = sys.argv[4]; outdir = sys.argv[5]
    n = 12 if mode == 'dc' else 9; cl = X.cells(n, k)
    nums = [a for a in sys.argv[6:] if a.isdigit()]
    first = int(nums[0]) if len(nums) == 2 else 0; last = int(nums[1]) if len(nums) == 2 else len(cl); run = 'run' in sys.argv
    tmo = float(dict(a.split('=') for a in sys.argv if '=' in a).get('timeout', 60))
    os.makedirs(outdir, exist_ok=True); tag = 'n1_%s_%s_k%d_p%d' % (mode, mspec.replace(',', '_'), k, p)
    man = open(os.path.join(outdir, tag + '.manifest'), 'a'); t0 = time.time(); stats = {}
    for idx in range(first, min(last, len(cl))):
        names, polys = build(p, mspec, k, mode, cl[idx]); fn = os.path.join(outdir, '%s_c%03d.ms' % (tag, idx))
        if X.trivially_unit(polys): verdict = 'UNIT(constant-equation)'; extra = ''
        else:
            X.write_msolve(fn, names, p, polys); verdict = 'not-run'; extra = ''
            if run:
                v, nb, dt = X.run_msolve(fn, timeout=tmo); verdict = v; extra = ' basis=%s time=%.2fs' % (nb, dt)
                if v == 'UNIT':
                    os.remove(fn)
                    if os.path.exists(fn + '.gb'): os.remove(fn + '.gb')
        stats[verdict] = stats.get(verdict, 0) + 1
        man.write('%s cell=%d pivots=%s nvars=%d npolys=%d verdict=%s%s\n' % (os.path.basename(fn), idx, cl[idx], len(names), len(polys), verdict, extra)); man.flush()
    print('%s cells %d..%d: %s  (%.0fs)' % (tag, first, min(last, len(cl)) - 1, stats, time.time() - t0))
if __name__ == '__main__': main()
