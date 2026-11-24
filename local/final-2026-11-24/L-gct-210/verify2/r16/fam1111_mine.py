# verify2 r16: exact check of reg2 R11-3 family (1,1,1,1|1,1) '1111_11a': level identically in a; dim T_1 <= 9 for EVERY a (and a = infinity);
# sigma_2-isotropic bound. Own code (cofactor first-order condition; 16x16 minors via exact evaluation/interpolation in a).
import sympy as sp, itertools, random
a=sp.Symbol('a'); P=sp.symbols('p0:6')
def row(i,v): M=sp.zeros(5,5); M[i,:]=sp.Matrix([v]); return M
def col(m,v): M=sp.zeros(5,5); M[:4,m]=sp.Matrix(v); return M
def gens(u0,u1): return [row(0,u0),row(1,u1),row(2,[0,-3,1,1,1]),row(3,[-4,1,1,1,1]),col(0,[1,1,-2,0]),col(1,[1,-1,0,0])]
def perm(A):
    n=A.shape[0]; return sp.expand(sum(sp.prod([A[i,f[i]] for i in range(n)]) for f in itertools.permutations(range(n))))
def system(G):
    Y=sum((P[k]*G[k] for k in range(6)),sp.zeros(5,5)); M=sp.ones(5,5)+Y
    lev=perm(M)
    cof={(i,j):perm(M.extract([k for k in range(5) if k!=i],[l for l in range(5) if l!=j])) for i in range(5) for j in range(5)}
    mons=set()
    for e in cof.values(): mons|=set(sp.Poly(e,*P).monoms())
    A=sp.Matrix([[sp.Poly(cof[(i,j)],*P).coeff_monomial(m) for i in range(5) for j in range(5)] for m in sorted(mons)])
    return lev,A
G=gens([0,0,-1-a,1,a],[0,0,1-a,1+2*a,-2-a])
lev,A=system(G); print('perm(J+Y) =',sp.simplify(lev),'(level iff 120)')
print('dim M =',sp.Matrix([list(g) for g in G]).subs(a,sp.Rational(3,7)).rank(),'(at a = 3/7)')
A=A.applyfunc(sp.expand)
r0=A.subs(a,sp.Rational(5,11)).rank(); print('generic rank of the T_1 matrix:',r0,' => generic dim T_1 =',25-r0)
# 16x16 minors as polynomials in a: pick row/col sets from random rational points, interpolate det exactly.
def minor_poly(rows,cols):
    sub=A.extract(rows,cols); deg=sum(max([sp.degree(e,a) if e!=0 else 0 for e in sub.row(i)]) for i in range(sub.rows))
    pts=[sp.Rational(k,3) for k in range(1,deg+2)]; vals=[sub.subs(a,t).det() for t in pts]
    return sp.factor(sp.interpolate(list(zip(pts,vals)),a))
random.seed(5); polys=[]
for trial in range(4):
    a0=sp.Rational(random.randint(1,50),random.randint(51,90)); B=A.subs(a,a0)
    _,pr=B.T.rref(); rows=list(pr)[:16]; _,pc=B.extract(rows,list(range(25))).rref(); cols=list(pc)[:16]
    f=minor_poly(rows,cols); polys.append(f); print('minor',trial,': ',str(f)[:150])
g=polys[0]
for f in polys[1:]: g=sp.gcd(g,f)
print('gcd of the minors:',g,' => rank >= 16 for all a off its roots')
# the point at infinity of the a-line
lev,Ai=system(gens([0,0,-1,0,1],[0,0,-1,2,-1])); print('a = infinity: level',lev==120,' dim T_1 =',25-Ai.rank())
