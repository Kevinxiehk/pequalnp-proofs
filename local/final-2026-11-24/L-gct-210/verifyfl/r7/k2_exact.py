"""exact (char 0, Q(w)) check of the two-column control K_2 = span(zeta (e0-e1)^T, zb e2^T, zb e3^T, h e3^T): C(Y) - 24*1 in C (e0 - e1)."""
import sympy as sp, itertools
w = sp.symbols('w'); x = sp.symbols('x1:5')
zeta = [1, w, w**2, 0]; zb = [1, w**2, w, 0]; h = [1, 1, 1, -3]
def outer(u, v): return sp.Matrix(4, 5, lambda a, c: u[a] * v[c])
Y = x[0] * outer(zeta, [1, -1, 0, 0, 0]) + x[1] * outer(zb, [0, 0, 1, 0, 0]) + x[2] * outer(zb, [0, 0, 0, 1, 0]) + x[3] * outer(h, [0, 0, 0, 1, 0])
def perm(M):
    return sp.expand(sum(sp.prod([M[i, f[i]] for i in range(4)]) for f in itertools.permutations(range(4))))
def red(e): return sp.rem(sp.Poly(sp.expand(e), w), sp.Poly(w**2 + w + 1, w)).as_expr()
C = []
for j in range(5):
    M = sp.ones(4, 4) + Y[:, [c for c in range(5) if c != j]]
    C.append(sp.expand(red(perm(M))))
print('C2-24, C3-24, C4-24 :', [sp.simplify(C[j] - 24) for j in (2, 3, 4)])
print('C0 + C1 - 48        :', sp.simplify(C[0] + C[1] - 48))
print('column sums zero    :', all(sp.simplify(sum(Y[a, c] for a in range(4)).subs(w**2, -w - 1)) == 0 for c in range(5)))
print('thetahat = C0 - 24  :', sp.factor(C[0] - 24))
