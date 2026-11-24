# round 10 target 2: polynomial parametrisation of the (ii-g) row-deformation curves of (2,1,1|2)(ii).
# b, c are PROJECTIVE sum-zero vectors in C^4 (the family 211ii uses b = (1,b2,b3,-1-b2-b3), c = (1,c2,c3,-1-c2-c3); scaling a basis element
# does not change the space).  rel01 = {b isotropic, <b,c> = 0, ...} ; rel02 = {c isotropic, <b,c> = 0, ...}.
# Isotropic sum-zero point over Q(w), w^2+w+1=0: p = (1, w, w^2, 0).  Conic parametrisation: x(s) = Q(q) p - 2 B(p,q) q, q = q0 + s q1,
# q0 = (1,0,0,-1), q1 = (0,1,0,-1).
import sympy as sp
s,w=sp.symbols('s w')
def red(e): return sp.rem(sp.expand(e), w**2+w+1, w)
p=sp.Matrix([1,w,w**2,0]); q=sp.Matrix([1,0,0,-1])+s*sp.Matrix([0,1,0,-1])
dot=lambda x,y: sum(x[i]*y[i] for i in range(4))
x=(dot(q,q)*p-2*dot(p,q)*q).applyfunc(red)
print('x(s) =',list(x)); print('sum =',red(sum(x)),' <x,x> =',red(dot(x,x)))
open('xs.txt','w').write(';'.join(str(e) for e in x))
