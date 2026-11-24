# e5_check.py: for each survivor and its chosen triple S, the pivot = 0 sub-family: is it inadmissible ((E3))?
import sys, ast, glob, re, subprocess
import sympy as sp
I = sp.I
txt = open('/home/kevxhk/work/L-gct-210/leanzbf/surv_families.txt').read()
summ = open('/home/kevxhk/work/L-gct-210/leanzbf/e5_summary.txt').read()
for blk in txt.split('== ')[1:]:
    head = blk.splitlines()[0].split()
    s12, s13, eps = head[0], head[1], int(head[2])
    fam = [sp.Matrix(sp.sympify(l.strip())) for l in blk.splitlines() if l.strip().startswith('[')]
    sb = summ.split('== %s %s %d' % (s12, s13, eps))[1].split('==')[0]
    m = re.search(r'S \((\d), (\d), (\d)\) n0 = (.*?)  z = (\[.*?\])\n\s+pivot y(\d) \(z = (.*?)\)', sb)
    if not m:
        print(s12, s13, eps, 'no constant-direction S'); continue
    S = tuple(int(m.group(i)) for i in (1, 2, 3)); piv = sp.sympify(m.group(7))
    P = sp.symbols('p0:%d' % len(fam))
    # restricted family: params with piv = 0
    coeffs = [sp.expand(piv).coeff(p) for p in P]
    Mrow = sp.Matrix([coeffs])
    ns = Mrow.nullspace()
    vecs = [sum((ns_k[i] * fam[i] for i in range(len(fam))), sp.zeros(10, 1)) for ns_k in ns]
    q12 = [1 if c == '1' else 0 for c in s12]; q13 = [1 if c == '1' else 0 for c in s13]
    def inspan(parts, base):
        Bm = sp.Matrix(base).T
        r0 = Bm.rank()
        return all(sp.Matrix.hstack(Bm, sp.Matrix(v)).rank() == r0 for v in parts)
    m3 = inspan([list(v[5:10]) for v in vecs], [[1] * 5, q13])
    m2 = inspan([list(v[0:5]) for v in vecs], [[1] * 5, q12])
    print(s12, s13, eps, 'S', S, 'pivot', piv, '| pivot=0 subfamily dim', len(vecs), '| M3 in span(1,1_Q13):', m3, '| M2 in span(1,1_Q12):', m2)
