# leanfl r15: Singular lift cofactors -> Lean certificate theorems (generic CommRing R)
# usage: python3 -I cof2lean.py NAME EQS NVARS QCOF PCOF P OUT.lean.part
import sympy as sp, sys, functools
name, eqf, nv, qf, pf, P, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5], int(sys.argv[6]), sys.argv[7]
vs = sp.symbols('t0:%d' % nv)
loc = {str(v): v for v in vs}
rd = lambda s: [sp.sympify(x.strip().rstrip(',').replace('^', '**'), locals=loc) for x in s.split('\n') if x.strip()]
F = [sp.expand(e) for e in rd(open(eqf).read())]
def lean(e):
    s = str(sp.expand(e)).replace('**', '^')
    return s
binders = '(' + ' '.join(str(v) for v in vs) + ' : R)'
hyps = ' '.join('(h%d : %s = 0)' % (i, lean(f)) for i, f in enumerate(F))
o = []
if qf != '-':
    C = rd(open(qf).read())
    d = functools.reduce(sp.ilcm, [sp.Poly(c, *vs).coeffs()[i].q for c in C for i in range(len(sp.Poly(c, *vs).coeffs()))], 1)
    Ci = [sp.expand(d * c) for c in C]
    assert sp.expand(sum(c * f for c, f in zip(Ci, F)) - d) == 0
    o.append('theorem %s_Q {R : Type} [CommRing R] %s\n    %s :\n    (%d : R) = 0 := by\n  linear_combination %s\n' % (
        name, binders, hyps, d, ' + '.join('(%s) * h%d' % (lean(c), i) for i, c in enumerate(Ci))))
    print('Q: d =', d, 'cofactor terms', sum(len(sp.Poly(c, *vs).terms()) for c in Ci))
if pf != '-':
    C = rd(open(pf).read())
    S = sp.expand(sum(c * f for c, f in zip(C, F)))
    R1 = sp.Poly(1 - S, *vs)
    assert all(int(c) % P == 0 for c in R1.coeffs())
    G = sp.expand((1 - S) / P)
    o.append('theorem %s_P {R : Type} [CommRing R] %s\n    %s :\n    ∃ g : R, 1 = %d * g :=\n  ⟨%s, by linear_combination %s⟩\n' % (
        name, binders, hyps, P, lean(G), ' + '.join('(%s) * h%d' % (lean(c), i) for i, c in enumerate(C))))
    print('P: cofactor terms', sum(len(sp.Poly(c, *vs).terms()) for c in C), 'G terms', len(sp.Poly(G, *vs).terms()))
open(out, 'w').write('\n'.join(o))
