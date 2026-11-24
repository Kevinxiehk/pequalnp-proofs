# Data for the next-round Lean generator: (II,II,I) local patterns under rule R
# (p = corner of pair 12, q in Q2^12, s in Q3^12; C23 splits S). Exact arithmetic over Q(i) (Gaussian Fractions).
import itertools
from fractions import Fraction as Fr
class G:  # Gaussian rational a + b i
    def __init__(s, a, b=0): s.a, s.b = Fr(a), Fr(b)
    def __add__(s, o): o = o if isinstance(o, G) else G(o); return G(s.a + o.a, s.b + o.b)
    __radd__ = __add__
    def __neg__(s): return G(-s.a, -s.b)
    def __sub__(s, o): return s + (-(o if isinstance(o, G) else G(o)))
    def __rsub__(s, o): return G(o) - s
    def __mul__(s, o): o = o if isinstance(o, G) else G(o); return G(s.a*o.a - s.b*o.b, s.a*o.b + s.b*o.a)
    __rmul__ = __mul__
    def inv(s): n = s.a*s.a + s.b*s.b; return G(s.a/n, -s.b/n)
    def __truediv__(s, o): o = o if isinstance(o, G) else G(o); return s * o.inv()
    def iszero(s): return s.a == 0 and s.b == 0
    def __repr__(s): return f'({s.a}+{s.b}i)'
def solve(rel):  # rel: list of rows over 9 unknowns (Fractions); returns (pivots, free, M) with tau = M * free_values
    A = [r[:] for r in rel]; piv = []; r = 0
    for c in range(9):
        k = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if k is None: continue
        A[r], A[k] = A[k], A[r]; pv = A[r][c]; A[r] = [x / pv for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c]; A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        piv.append(c); r += 1
    free = [c for c in range(9) if c not in piv]
    M = [[Fr(0)] * len(free) for _ in range(9)]
    for l, f in enumerate(free): M[f][l] = Fr(1)
    for i, c in enumerate(piv):
        for l, f in enumerate(free): M[c][l] = -A[i][f]
    return piv, free, M
def perm3(X): return sum((X[0][a]*X[1][b]*X[2][c] for a, b, c in itertools.permutations(range(3))), G(0))
out = []
for lab13 in itertools.product((1, 2, 3), repeat=3):
    for c23 in itertools.product((0, 1), repeat=3):
        if len(set(c23)) == 1 or c23[0] == 0: continue        # C23 splits S; normalise p in C23
        for e12 in (1, -1):
            for e13 in (1, -1):
                w2 = [G(0, e12), G(1), G(-1)]
                w3 = [G(0, e13) if l == 1 else G(1 if l == 2 else -1) for l in lab13]
                rat = [w3[k] / w2[k] for k in range(3)]
                sgn = [(-1 if c23[k] else 1) for k in range(3)]
                th = rat[0] / G(sgn[0])
                if not all((rat[k] - th * G(sgn[k])).iszero() for k in range(3)): continue
                rel = []
                for i in range(3):
                    rel.append([Fr(1) if v // 3 == i else Fr(0) for v in range(9)])
                v = [Fr(0)] * 9; v[0*3+2] += 1; v[1*3+1] += 1; rel.append(v)
                v = [Fr(0)] * 9
                for k in range(3):
                    if lab13[k] == 3: v[0*3+k] += 1
                    if lab13[k] == 2: v[2*3+k] += 1
                rel.append(v)
                v = [Fr(0)] * 9
                for k in range(3):
                    if c23[k]: v[1*3+k] += 1; v[2*3+k] -= 1
                rel.append(v)
                piv, free, M = solve(rel)
                if len(free) != 3: out.append((lab13, c23, e12, e13, 'rank', len(piv))); continue
                found = None
                for x0 in itertools.product(range(-2, 3), repeat=3):
                    tau = [sum((M[r][l] * x0[l] for l in range(3)), Fr(0)) for r in range(9)]
                    X = [[G(tau[3*i+k]) / ([G(1)]*3, w2, w3)[i][k] for k in range(3)] for i in range(3)]
                    p = perm3(X)
                    if not p.iszero(): found = (x0, p); break
                out.append((lab13, c23, e12, e13, free, found))
ok = [o for o in out if len(o) == 6 and o[5] is not None]
print('consistent patterns:', len(out), ' with 3 parameters and a nonzero point:', len(ok))
for o in out: print(o)
