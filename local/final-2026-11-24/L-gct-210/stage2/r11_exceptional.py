# Exceptional parameter values for the symbolic FO2-joint run of D04-PROP alpha = (1,1,-1,-1) [NOTES-stage2 R11-1]:
#   E = {sg : dim T_1(X_sg) > 14}  U  {sg : the cleared-denominator complement basis Qm(sg) is not independent modulo X_sg}.
# For sg outside E the symbolic chart computation is valid. Method: exact sympy; gcd of determinants of random integer compressions.
import sys, itertools, random, sympy as sp
random.seed(int(sys.argv[1]) if len(sys.argv)>1 else 1)
sg=sp.Symbol('sg'); z=sp.symbols('z1:6')
def mat(rows):
    M=sp.zeros(5,5)
    for (i,j),v in rows.items(): M[i,j]=v
    return M
Bs=[mat({(1,0):sg,(2,0):-1-sg,(4,0):1}), mat({(3,0):-4,(3,1):1,(3,2):1,(3,3):1,(3,4):1}), mat({(3,1):1,(3,2):1,(3,3):-1,(3,4):-1}),
    mat({(4,1):1,(4,2):-1}), mat({(4,3):1,(4,4):-1})]
m=sum((z[k]*Bs[k] for k in range(5)),sp.zeros(5,5)); U=sp.ones(5,5)+m
def permsym(M):
    n=M.shape[0]
    return sp.expand(sum(sp.prod([M[i,p[i]] for i in range(n)]) for p in itertools.permutations(range(n))))
def minor(M,rows,cols): return M.extract([r for r in range(5) if r not in rows],[c for c in range(5) if c not in cols])
C=[permsym(minor(U,[i],[j])) for i in range(5) for j in range(5)]
t=sp.symbols('t0:25'); expr=sp.expand(sum(t[k]*C[k] for k in range(25)))
eqs=sp.Poly(expr,*z).coeffs()
A=sp.Matrix([[sp.Poly(e,*t).coeff_monomial(t[k]) for k in range(25)] for e in eqs])
print('T_1 system:',A.shape,flush=True)
def rnd(r,c): return sp.Matrix(r,c,lambda i,j: random.randint(-3,3))
g1=0
for _ in range(3):
    d=sp.factor((rnd(11,A.rows)*A*rnd(25,11)).det()); g1=sp.gcd(g1,d) if g1!=0 else d
print('rank-11 test polynomial (dim T_1 > 14 only at its roots):',sp.factor(g1),flush=True)
NS=A.nullspace(); T1=sp.Matrix.hstack(*NS).T
Xm=sp.Matrix([[Bs[k][i,j] for i in range(5) for j in range(5)] for k in range(5)])
comp=[]; cur=Xm
for r in range(T1.rows):
    cand=sp.Matrix.vstack(cur,T1.row(r))
    if cand.rank()>cur.rank(): comp.append(T1.row(r)); cur=cand
Qm=sp.Matrix.vstack(*[ (lambda r: (r*sp.lcm([sp.fraction(sp.together(e))[1] for e in r])).applyfunc(sp.expand))(r) for r in comp])
M14=sp.Matrix.vstack(Xm,Qm)
g2=0
for _ in range(3):
    d=sp.factor((M14*rnd(25,14)).det()); g2=sp.gcd(g2,d) if g2!=0 else d
print('complement test polynomial (basis degenerates only at its roots):',sp.factor(g2),flush=True)
