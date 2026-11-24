"""factor the eliminating polynomial of the B0 Z-set over GF(p) (sympy); prints the degrees of the irreducible factors and writes them."""
import sympy as sp, sys
p = 2147483629; M = sys.argv[1]
LL = sp.symbols('LL'); f = sp.Poly(sp.sympify(open('elim_%s.txt' % M).read().replace('\n', '')), LL, modulus=p)
c, facs = f.factor_list()
print(M, 'degree', f.degree(), '-> factors (degree^mult):', sorted([(g.degree(), e) for g, e in facs]))
with open('factors_%s.txt' % M, 'w') as out:
    for g, e in facs: out.write(str(g.as_expr()).replace('**', '^') + '\n')
