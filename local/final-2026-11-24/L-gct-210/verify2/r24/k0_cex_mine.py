# verify2 r24: exact check of ncol's CONJECTURE K0 counterexample (NOTES-ncol R11.7/R11.8), my own code, direct permanent expansion.
# S = span( (H nu1) a^T , (H nu2) b^T ), nu1 = (1,w,w^2), nu2 = (1,w^2,w) Walsh vectors, w^2+w+1 = 0; Y = x (H nu1) a^T + y (H nu2) b^T (4x5).
# Checks: level (N(J4+Y) = sum_j perm(J4 + Y minus col j) = 120 identically in x,y), defect c(Y)_j = perm(J4 + Y minus col j) - 24,
# e = dim span{c(Y)} (via coefficient vectors in x,y), the defect line, zero-freeness.
import sympy as sp, sys
from itertools import permutations
w,x,y=sp.symbols('w x y')
def red(e): return sp.expand(sp.rem(sp.expand(e),w**2+w+1,w))
H=sp.Matrix([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]])
nu1=sp.Matrix([1,w,w**2]); nu2=sp.Matrix([1,w**2,w])
def perm(M):
    n=M.rows; return sum(sp.prod([M[i,p[i]] for i in range(n)]) for p in permutations(range(n)))
def check(a,b,label):
    a=[sp.Rational(v) for v in a]; b=[sp.Rational(v) for v in b]
    u1=(H*nu1).applyfunc(red); u2=(H*nu2).applyfunc(red)
    Y=sp.Matrix(4,5,lambda r,j: x*u1[r]*a[j]+y*u2[r]*b[j]).applyfunc(red)
    print('==',label,' a =',a,' b =',b,'  H nu1 =',list(u1),' (row 0 zero:',u1[0]==0 and u2[0]==0,')')
    c=[]
    for j in range(5):
        M=sp.Matrix(4,4,lambda r,q: 1+Y[r,[k for k in range(5) if k!=j][q]])
        c.append(red(perm(M)-24))
    N=red(sum(c))
    print('  level: N(J4+Y)-120 =',N)
    # coefficient vectors of c over monomials in x,y (coefficients in Q(w) as a + b w)
    mons=set()
    for cj in c: mons|=set(sp.Poly(cj,x,y).monoms())
    mons=sorted(mons)
    rows=[]
    for m in mons:
        rows.append([sp.Poly(cj,x,y).coeff_monomial(x**m[0]*y**m[1]) for cj in c])
    Mx=sp.Matrix(rows)
    # rank over Q(w): split each entry a+b w into two rational rows (w is irrational, so rank over Q(w) = rank of the stacked real/omega parts? no:)
    # use exact rank over Q(w) via substitution w -> exact algebraic number
    wv=sp.Rational(-1,2)+sp.sqrt(3)*sp.I/2
    Mn=Mx.subs(w,wv).applyfunc(sp.nsimplify)
    r=Mn.rank(simplify=True)
    print('  monomials',mons,' e = rank =',r)
    # defect line: first nonzero row normalised
    for row in rows:
        if any(v!=0 for v in row):
            k=[v for v in row if v!=0][-1]
            line=[sp.simplify((v/k).subs(w,wv)) for v in row]
            print('  defect line (normalised):',line,' zero-free:',all(v!=0 for v in line)); break
    e3=sum(a[i]*a[j]*a[k] for i in range(5) for j in range(i+1,5) for k in range(j+1,5))
    print('  e3(a) =',e3,' sum a b - A B =',sum(ai*bi for ai,bi in zip(a,b))-sum(a)*sum(b))
check((-3,-3,7,14,-21),(1,-1,0,0,0),'R11.7 counterexample')
check((1,1,-3,-3,6),(1,-1,0,0,0),'R11.8 b22 rational member')
