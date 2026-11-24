# EXACT common rank-drop locus of the B_c, lean version of r16_cofinterp.py [NOTES-stage2 R17]: lattice determinants are CACHED (pickle), the
# known factor lam^m * D^n * (content) is divided out of every lattice value before interpolation, P(c) is NOT factored, and the c-coefficient ideal
# is written as a Singular script (minimal associated primes over QQ, exceptional factors saturated).
# usage: r17_cofinterp2.py CACHE INDEX_i [EXC_FACTORS e.g. "lam,a1,a1+a2+a3-4"]
import sys, os, pickle, sympy as sp
from sympy.polys.matrices import DomainMatrix
ck=sys.argv[1]; i=int(sys.argv[2]); excs=sys.argv[3] if len(sys.argv)>3 else ''
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(ck,'rb'))
loc={str(p):p for p in par}; EXC=[sp.sympify(x,locals=loc) for x in excs.split(',') if x]
R=sp.QQ[tuple(par)]; d=nq-1; idx=[j for j in range(nq) if j!=i]
mons=[(p,q,d-p-q) for p in range(d+1) for q in range(d+1-p)]
cachef=ck.replace('.pkl','_latdets.pkl'); vals=pickle.load(open(cachef,'rb')) if os.path.exists(cachef) else {}
for m in mons:
    if m in vals: continue
    B=(m[0]*Gs[1]+m[1]*Gs[2]+m[2]*Gs[3]).extract(idx,idx)
    vals[m]=DomainMatrix.from_Matrix(B).convert_to(R).det().as_expr(); pickle.dump(vals,open(cachef,'wb')); print('lattice point',m,flush=True)
# divide out the exceptional factors as far as they divide every nonzero lattice value
P=lambda e: sp.Poly(sp.expand(e),*par)
polys={m:P(v) for m,v in vals.items()}
for f in EXC:
    F=P(f)
    while all(pv.is_zero or pv.rem(F).is_zero for pv in polys.values()):
        polys={m:(pv if pv.is_zero else pv.quo(F)) for m,pv in polys.items()}; print('divided out',f,flush=True)
c1,c2,c3=sp.symbols('c1 c2 c3')
V=sp.Matrix([[sp.Integer(p)**a*sp.Integer(q)**b*sp.Integer(r)**g for (a,b,g) in mons] for (p,q,r) in mons]); Vi=V.inv()
coeffs=[]
for n in range(len(mons)):
    acc=sp.Poly(0,*par)
    for m in range(len(mons)):
        if Vi[n,m]!=0 and not polys[mons[m]].is_zero: acc=acc+polys[mons[m]]*sp.Rational(Vi[n,m])
    coeffs.append(acc)
nz=[c for c in coeffs if not c.is_zero]
print('nonzero c-coefficients:',len(nz),' max total degree',max(c.total_degree() for c in nz),flush=True)
g=nz[0]
for c in nz[1:]: g=g.gcd(c)
print('gcd of the c-coefficients:',sp.factor(g.as_expr()),flush=True)
red=[c.quo(g) for c in nz]
out=ck.replace('.pkl','_cofideal.sing')
E=sp.prod(EXC) if EXC else 1
open(out,'w').write('LIB "primdec.lib";\nring r=0,(w,%s),dp;\nideal I=%s,\n1-w*(%s);\nideal J=eliminate(I,w);\nring s=0,(%s),dp;\nideal J=imap(r,J);\nlist L=minAssGTZ(J);\nL;\nquit;\n'%(','.join(map(str,par)),',\n'.join(str(c.as_expr()).replace('**','^') for c in red),str(sp.expand(E)).replace('**','^'),','.join(map(str,par))))
print('Singular script for the exact locus (outside exceptional):',out,flush=True)
print('locus = V(gcd) U V(reduced coefficients); run: Singular -q',out,flush=True)
