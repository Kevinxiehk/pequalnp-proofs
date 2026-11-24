# verify2 r24: EXACT check of rows' (SM4) counterexample over Q(sqrt3, i): Y = H [y1 y2 y3 y4 0] (Walsh coordinates), strongly level?
import sympy as sp, itertools
s=sp.sqrt(3); I=sp.I; t=sp.Symbol('t')
y1=sp.Matrix([(s+1)/2, -I*(s-1)/2, 0]); y2=sp.Matrix([(1-s)/2, I*(s+1)/2, 0]); y3=sp.Matrix([sp.Rational(1,2), I/2, 0]); y4=-y3; y5=sp.zeros(3,1)
H=sp.Matrix([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]])
Y=sp.Matrix.hstack(*[H*y for y in (y1,y2,y3,y4,y5)]).applyfunc(sp.expand)
f=(y1+y2+y3+y4+y5).applyfunc(sp.simplify); print('row sum f (Walsh) =',list(f),'  <f,f> =',sp.simplify((f.T*f)[0]))
print('nonzero columns:',[k for k in range(5) if any(sp.simplify(Y[i,k])!=0 for i in range(4))])
print('column sums of Y (column-centred?):',[sp.simplify(sum(Y[:,k])) for k in range(5)])
def perm4(M): return sp.expand(sum(sp.prod([M[i,p[i]] for i in range(4)]) for p in itertools.permutations(range(4))))
J=sp.ones(4,5)
for j in range(5):
    M=(J+t*Y); M=M.extract(list(range(4)),[c for c in range(5) if c!=j])
    d=sp.simplify(sp.expand(perm4(M))-24)
    print('deletion',j,': perm(J + tY minus col j) - 24 =',d)
