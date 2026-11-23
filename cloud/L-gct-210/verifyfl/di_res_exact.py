import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""EXACT (rational arithmetic) proof of (F1): distinct isotropic lines v = v(t), v' = v(u) with tau(v^2 v') = 0 and [v,v,v',v'] = 0
   are zero-row pairs.  Res_u( E(u,t), P(t,u) ) is computed exactly as a polynomial in t and factored."""
from fractions import Fraction as Fr
import itertools
# polynomials in t as lists of Fractions (low degree first)
def padd(a, b):
    n = max(len(a), len(b)); return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]
def pmul(a, b):
    r = [Fr(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): r[i + j] += x * y
    return r
def pscale(a, c): return [c * x for x in a]
def ptrim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0: a.pop()
    return a
def pdivmod(a, b):
    a = ptrim(a); b = ptrim(b); q = [Fr(0)] * max(1, len(a) - len(b) + 1)
    while len(a) >= len(b) and any(x != 0 for x in a):
        c = a[-1] / b[-1]; k = len(a) - len(b); q[k] = c
        a = ptrim(padd(a, pscale([Fr(0)] * k + b, -c)))
        if len(a) == 1 and a[0] == 0: break
    return ptrim(q), a
T = [Fr(0), Fr(1)]
def tp(k): return [Fr(0)] * k + [Fr(1)]
# E(u,t) = (t^3/2) u^2 + (1 + t^4/4) u + 2t     (coefficients in u, high to low)
Ecoef = [pscale(tp(3), Fr(1, 2)), padd([Fr(1)], pscale(tp(4), Fr(1, 4))), pscale(tp(1), Fr(2))]
# P = 2 (u^2 + 4 t u + t^2)^2 - (3/2)(t^2 u^2 - 4)^2   as a polynomial in u with coefficients in Q[t]
def upoly_mul(A, B):      # lists of t-polys, low degree in u first
    R = [[Fr(0)] for _ in range(len(A) + len(B) - 1)]
    for i, x in enumerate(A):
        for j, y in enumerate(B): R[i + j] = padd(R[i + j], pmul(x, y))
    return R
A1 = [tp(2), pscale(tp(1), Fr(4)), [Fr(1)]]            # t^2 + 4t u + u^2
A2 = [[Fr(-4)], [Fr(0)], tp(2)]                         # -4 + t^2 u^2
P = [padd(pscale(x, Fr(2)), pscale(y, Fr(-3, 2))) for x, y in zip(upoly_mul(A1, A1), upoly_mul(A2, A2))]
Pcoef = [ptrim(c) for c in P[::-1]]                     # high to low in u (degree 4)
# Sylvester matrix (6x6) with polynomial entries; determinant by cofactor expansion over polynomials
def sylvester(F, G):      # F degree m (len m+1), G degree n
    m, n = len(F) - 1, len(G) - 1; M = [[[Fr(0)] for _ in range(m + n)] for _ in range(m + n)]
    for i in range(n):
        for j, c in enumerate(F): M[i][i + j] = c
    for i in range(m):
        for j, c in enumerate(G): M[n + i][i + j] = c
    return M
def pdet(M):
    n = len(M)
    if n == 1: return M[0][0]
    tot = [Fr(0)]
    for j in range(n):
        if all(x == 0 for x in M[0][j]): continue
        minor = [row[:j] + row[j + 1:] for row in M[1:]]
        tot = padd(tot, pscale(pmul(M[0][j], pdet(minor)), Fr((-1) ** j)))
    return tot
R = ptrim(pdet(sylvester(Ecoef, Pcoef)))
print('Res_u(E, P): degree', len(R) - 1, ' lowest nonzero power t^%d' % next(i for i, x in enumerate(R) if x != 0))
Z = [Fr(16), 0, 0, 0, Fr(-56), 0, 0, 0, Fr(1)]          # t^8 - 56 t^4 + 16 : the eight zero-row parameters
k = next(i for i, x in enumerate(R) if x != 0); rem = R[k:]; mult = 0
while True:
    q, r = pdivmod(rem, Z)
    if any(x != 0 for x in r): break
    rem = q; mult += 1
print('Res = t^%d * (t^8 - 56 t^4 + 16)^%d * cofactor, cofactor =' % (k, mult), [str(x) for x in ptrim(rem)])
# the factor (t - u): does E(u,t) = P = 0 have solutions with u = t ?  E(t,t) = 3t + 3t^5/4, P(t,t) = 72 t^4 - (3/2)(t^4-4)^2
Ett = [Fr(0), Fr(3), 0, 0, 0, Fr(3, 4)]; Ptt = padd(pscale(tp(4), Fr(72)), pscale(pmul([Fr(-4), 0, 0, 0, Fr(1)], [Fr(-4), 0, 0, 0, Fr(1)]), Fr(-3, 2)))
print('gcd check on the diagonal: E(t,t) = 3t(1 + t^4/4) vanishes at t = 0 and t^4 = -4; P(t,t) at t^4 = -4: ', 72 * (-4) - Fr(3, 2) * 64, ' at t = 0:', Ptt[0])
