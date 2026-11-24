"""exact check (sympy) for R8.8: for x in V (sum x = 0) and Y_x = (x/2) (1,1,1,1,-2)^T, the vector C(t Y_x) - 24*1 is a multiple of
m = (1,1,1,1,-4) for all t only if e_2(x) = e_3(x) = e_4(x) = 0.  Prints the t^k-coefficients of C_j(t Y_x) - 24 and the obstruction."""
import sympy as sp, itertools
x0, x1, x2, t = sp.symbols('x0 x1 x2 t'); x = [x0, x1, x2, -x0 - x1 - x2]
w = [sp.Rational(1, 2)] * 4 + [-1]
Y = sp.Matrix(4, 5, lambda a, c: x[a] * w[c])
def perm(M): return sp.expand(sum(sp.prod([M[i, f[i]] for i in range(4)]) for f in itertools.permutations(range(4))))
Cs = [sp.expand(perm(sp.ones(4, 4) + t * Y[:, [c for c in range(5) if c != j]]) - 24) for j in range(5)]
e = lambda k: sp.expand(sum(sp.prod(c) for c in itertools.combinations(x, k)))
for k in (1, 2, 3, 4):
    co = [sp.factor(sp.Poly(Cj, t).coeff_monomial(t**k)) for Cj in Cs]
    # defect line condition: co_j = lam * m_j with m = (1,1,1,1,-4): equivalently co_0 = co_1 = co_2 = co_3 and co_4 = -4 co_0
    obstruction = sp.factor(co[4] + 4 * co[0])
    print('t^%d: C_0..C_3 coeff = %s ; C_4 coeff = %s ; C_4 + 4 C_0 = %s ; e_%d(x) = %s' % (k, co[0], co[4], obstruction, k, sp.factor(e(k))))
