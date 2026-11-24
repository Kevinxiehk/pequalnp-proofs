# verify2 r24: rows R21.4 hand claim (no case-G pencil in the coordinate-plane family): check P_4 = -w^2 (3 - t^2)/2 and the rank-1 identity.
import sympy as sp
from itertools import permutations
I=sp.I; t,w=sp.symbols('t w')
H=sp.Matrix([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]])
f=sp.Matrix([1,I,0]); fb=sp.Matrix([1,-I,0])
g=[-t*fb, t*fb, (1-w)*f, (1+w)*f]           # S1 = {1,2}: sum al = sum be = 0; S0 = {3,4}: sum = 2f
y=[(f-gk)/2 for gk in g]                     # g_k = f - 2 y_k
assert sp.simplify(sum(y,sp.zeros(3,1))-f)==sp.zeros(3,1)
Y=H*sp.Matrix.hstack(*y)
def perm(M):
    n=M.rows; return sp.expand(sum(sp.prod([M[i,p[i]] for i in range(n)]) for p in permutations(range(n))))
P4=perm(Y); print('P4 =',sp.factor(P4), '  matches -w^2(3-t^2)/2:', sp.expand(P4-(-w**2*(3-t**2)/2))==0)
# rank-1 identity: e3(Hx) vs x1 x2 x3 ; and P4 of rank one u c^T = 24 prod u prod c
x=sp.symbols('x1:4'); u=H*sp.Matrix(x)
e3=sp.expand(sum(u[a]*u[b]*u[c] for a in range(4) for b in range(a+1,4) for c in range(b+1,4)))
print('e3(Hx) =',sp.factor(e3))
