# EXACT common rank-drop locus of the B_c (all c at once) [NOTES-stage2 R16]: P(c) := cof_ii(c1 B1 + c2 B2 + c3 B3) is a homogeneous polynomial of
# degree nq-1 in c. Evaluate it exactly on the principal lattice {c in Z_{>=0}^3 : |c| = nq-1} (unisolvent for forms of that degree) and interpolate.
# rank B_c < nq-1 for ALL c  <=>  every c-coefficient of P vanishes. Output: the coefficient polynomials (content and exceptional factors removed),
# a Singular script computing the radical / minimal associated primes of their ideal, saturated by the exceptional factors.
# usage: r16_cofinterp.py CACHE INDEX_i   (i = pivot index of the constant kernel vector k, e.g. 6 for k = e7 - e6 normalised at 6... use r16_Kauto's)
import sys, pickle, itertools, sympy as sp
from sympy.polys.matrices import DomainMatrix
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(sys.argv[1],'rb')); i=int(sys.argv[2])
R=sp.QQ[tuple(par)]; d=nq-1; idx=[j for j in range(nq) if j!=i]
c1,c2,c3=sp.symbols('c1 c2 c3')
mons=[(p,q,d-p-q) for p in range(d+1) for q in range(d+1-p)]
vals=[]
for (p,q,r) in mons:
    B=(p*Gs[1]+q*Gs[2]+r*Gs[3]).extract(idx,idx)
    vals.append(DomainMatrix.from_Matrix(B).convert_to(R).det().as_expr()); print('lattice point',(p,q,r),'done',flush=True)
# interpolation: solve V * coeffs = vals with V[m][n] = c^alpha_n evaluated at lattice point m
alph=mons
V=sp.Matrix([[sp.Integer(p)**a*sp.Integer(q)**b*sp.Integer(r)**g for (a,b,g) in alph] for (p,q,r) in mons])
Vi=V.inv()
coeffs=[sp.expand(sum(Vi[n,m]*vals[m] for m in range(len(mons)))) for n in range(len(alph))]
Pc=sum(cf*c1**a*c2**b*c3**g for cf,(a,b,g) in zip(coeffs,alph))
# check on two random extra points
import random; random.seed(1)
for _ in range(2):
    cc=[random.randint(-5,5) for _ in range(3)]
    B=(cc[0]*Gs[1]+cc[1]*Gs[2]+cc[2]*Gs[3]).extract(idx,idx)
    assert sp.expand(DomainMatrix.from_Matrix(B).convert_to(R).det().as_expr()-Pc.subs({c1:cc[0],c2:cc[1],c3:cc[2]}))==0
print('interpolation verified at 2 extra points',flush=True)
print('P(c) factored:',str(sp.factor(Pc))[:3000],flush=True)
nz=[cf for cf in coeffs if cf!=0]; g=nz[0]
for cf in nz[1:]: g=sp.gcd(g,cf)
print('gcd of the c-coefficients (vanishes => rank drop for all c):',sp.factor(g),flush=True)
red=[sp.factor(sp.cancel(cf/g)) for cf in nz]
open(sys.argv[1].replace('.pkl','_cofideal.txt'),'w').write('\n'.join(str(sp.expand(x)) for x in red)+'\n')
print('reduced coefficient ideal written (%d generators); its zero set U V(gcd) is the exact common rank-drop locus'%len(red),flush=True)
