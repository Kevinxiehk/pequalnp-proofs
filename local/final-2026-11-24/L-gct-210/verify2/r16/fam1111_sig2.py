import sympy as sp, sys, itertools, time
src=open('fam1111_mine.py').read().split("A=A.applyfunc(sp.expand)")[0]; exec(src)
from sympy.polys.matrices import DomainMatrix
A=A.applyfunc(sp.expand); B=A.subs(a,sp.Rational(5,11)); _,pr=B.T.rref(); R=list(pr)[:16]
K=sp.QQ.frac_field(a); t0=time.time()
dm=DomainMatrix.from_Matrix(A.extract(R,list(range(25)))).convert_to(K)
N=dm.nullspace().to_Matrix(); print('nullspace over Q(a):',N.shape,'%.1f s'%(time.time()-t0))
T=[N.row(i).T for i in range(N.rows)]
# clear denominators per vector
T=[ (v*sp.lcm([sp.fraction(sp.together(e))[1] for e in v])).applyfunc(sp.cancel) for v in T]
def sig2(v):
    D=sp.Matrix(5,5,list(v)); return sum(D[i1,j1]*D[i2,j2] for (i1,i2) in itertools.combinations(range(5),2) for j1 in range(5) for j2 in range(5) if j1!=j2)
n=len(T); Q=sp.Matrix(n,n,lambda i,j: sp.factor(sp.expand((sig2(T[i]+T[j])-sig2(T[i])-sig2(T[j]))/2)))
print('sigma_1 on basis:',[sp.factor(sum(v)) for v in T][:3],'...')
ent=[e for e in Q if e!=0]; g=ent[0]
for e in ent[1:]: g=sp.gcd(g,e)
print('generic rank of sigma_2 form:',Q.subs(a,sp.Rational(5,11)).rank(),' gcd of all entries:',sp.factor(g))
den=[sp.factor(sp.fraction(sp.together(e))[1]) for e in T[0]]; print('basis denominators cleared; sample entry degrees',[sp.degree(sp.numer(sp.together(e)),a) for e in list(Q)[:5]])
