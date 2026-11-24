# GENERIC setup from a spec file (PAR, BS = 5 X-basis matrices, may contain parameters) [NOTES-stage2 R22-1]:
# T_1 rref, rank-jump test, complement, ALL coefficient forms (in z) of Q H(J+m) Q^T as in r14_D3A_fx.py; cache r22/cache_TAG.pkl.
# usage: r22_genset.py SPECFILE TAG
# Target 3: FO2-joint for the D003-PROP Case-A family over P^2_alpha (NOTES-stage2 R14-4), with the FULL set of forms q_m (m in X).
#   X = span{ kappa0 = (0,0,1,-1) e_0^T, kappa_s = (1,-1,0,0) e_0^T  (column 0, rows 1..4),  e_3 (x) (0; alpha),  e_4 (x) (0; W1), e_4 (x) (0; W2) },
#   alpha = (1, a2, a3, -1-a2-a3) (chart alpha_1 = 1; WLOG by S_4 on columns 1..4), W1, W2 a basis of alpha^perp cap 1^perp (valid for a2 != 1, which is
#   WLOG too: some coordinate of alpha differs from alpha_1 unless alpha is proportional to 1, impossible).
# Steps as r13_F2col_v2.py: T_1 by rref over Q(a2,a3), rank-jump polynomial, complement, forms = all coefficient matrices (in z) of Q H(J+m) Q^T,
# Rabinowitsch exclusion of bad loci, msolve on all charts (coefficients reduced mod p; FAILED reported separately).
# usage: r14_D3A.py CH [a2=..,a3=..]   env MSV (KB), CHARTS
import sys, itertools, subprocess, os, re, random, sympy as sp
exec(open('/home/kevxhk/work/L-gct-210/stage2/r15_msstr_fixed.py').read())
CH='0'; SPEC=sys.argv[1]; TAG=sys.argv[2] if len(sys.argv)>2 else 'gen'
spec={'sp':sp}; exec(open(SPEC).read(),spec)
par=spec['PAR']; Bs=spec['BS']; fix={}
A2=None
def mat(rows):
    M=sp.zeros(5,5)
    for (i,j),v in rows.items(): M[i,j]=v
    return M
zv=sp.symbols('z1:6'); m=sum((zv[k]*Bs[k] for k in range(5)),sp.zeros(5,5)); U=sp.ones(5,5)+m
def permsym(M):
    n=M.shape[0]
    if n==0: return sp.Integer(1)
    return sp.expand(sum(sp.prod([M[i,p[i]] for i in range(n)]) for p in itertools.permutations(range(n))))
def minor(M,rows,cols): return M.extract([r for r in range(5) if r not in rows],[c for c in range(5) if c not in cols])
C=[permsym(minor(U,[i],[j])) for i in range(5) for j in range(5)]
t=sp.symbols('t0:25'); expr=sp.expand(sum(t[k]*C[k] for k in range(25)))
eqs=sp.Poly(expr,*zv).coeffs()
Am=sp.Matrix([[sp.Poly(q,*t).coeff_monomial(t[k]) for k in range(25)] for q in eqs])
from sympy.polys.matrices import DomainMatrix
_dom=(sp.QQ.algebraic_field(sp.I).frac_field(*par) if par else sp.QQ.algebraic_field(sp.I)) if spec.get('QI') else (sp.QQ.frac_field(*par) if par else sp.QQ)
_R,piv=DomainMatrix.from_Matrix(Am).convert_to(_dom).rref(); R=_R.to_Matrix()[:len(piv),:]
free=[c for c in range(25) if c not in piv]
print('dim T_1 =',len(free),flush=True)
rkjump=sp.Integer(1)
if par:
    random.seed(11); g=0
    for _ in range(3):
        rr=sp.Matrix(len(piv),Am.rows,lambda i,j: random.randint(-3,3)); cc=sp.Matrix(25,len(piv),lambda i,j: random.randint(-3,3))
        _cm=DomainMatrix.from_Matrix(rr*Am*cc).convert_to(sp.QQ.algebraic_field(sp.I)[tuple(par)] if spec.get('QI') else sp.QQ[tuple(par)]); _d=_cm.det()
        dd=sp.factor(_d.as_expr() if hasattr(_d,'as_expr') else sp.sympify(str(_d))); g=sp.gcd(g,dd) if g!=0 else dd
    rkjump=sp.factor(g); print('rank-jump test polynomial:',rkjump,flush=True)
fs=sp.symbols('f0:%d'%len(free)); tv=[None]*25
for i,c in enumerate(free): tv[c]=fs[i]
for r,c in enumerate(piv): tv[c]=sp.together(-sum(R[r,cc]*tv[cc] for cc in free))
Xf=sp.Matrix([[Bs[k][c//5,c%5] for c in free] for k in range(5)])
random.seed(3); sub={p:sp.Rational(random.randint(2,9),random.randint(2,9)) for p in par}
chosen=None
for S in itertools.combinations(range(len(free)),len(free)-5):
    rest=[i for i in range(len(free)) if i not in S]
    if Xf.subs(sub).extract(list(range(5)),rest).det()!=0: chosen=list(S); restc=rest; break
detX=sp.factor(Xf.extract(list(range(5)),restc).det()); print('complement valid where det != 0:',detX,flush=True)
co=[fs[i] for i in chosen]; nq=len(co)
# complement basis vectors in C^25: set one complement coordinate to 1, the X-pivot free coords to 0
Qrows=[]
for i in range(nq):
    subs_={fs[j]:(1 if j==chosen[i] else 0) for j in range(len(free))}
    Qrows.append([sp.together(tv[c].subs(subs_)) for c in range(25)])
Qm=sp.Matrix(Qrows)
den=sp.lcm([sp.fraction(sp.together(e))[1] for e in Qm]); Qm=(Qm*den).applyfunc(lambda e: sp.expand(sp.cancel(e)))
print('complement scaled by',sp.factor(den),flush=True)
H=sp.zeros(25,25)
for i in range(5):
    for k in range(i+1,5):
        for j in range(5):
            for l in range(5):
                if j==l: continue
                v=permsym(minor(U,[i,k],[j,l])); H[5*i+j,5*k+l]=v; H[5*k+l,5*i+j]=v
F=(Qm*H*Qm.T).applyfunc(sp.expand)
monos=set()
for e in F:
    if e!=0: monos|=set(sp.Poly(e,*zv).monoms())
mats=[F.applyfunc(lambda e: sp.Poly(e,*zv).coeff_monomial(mo) if e!=0 else 0) for mo in sorted(monos)]
print('number of coefficient forms',len(mats),flush=True)

import pickle
mons=sorted(monos); i0=mons.index((0,0,0,0,0)); q0=mats[i0]; Bf=[M for k_,M in enumerate(mats) if k_!=i0]
pickle.dump((None,None,None,None,None,par,[q0]+Bf,co,nq,[den],detX,rkjump,fix),open('/home/kevxhk/work/L-gct-210/stage2/r22/cache_%s.pkl'%TAG,'wb'))
print('saved r22/cache_%s.pkl  (forms: q0 + %d coefficient forms, nq %d)'%(TAG,len(Bf),nq),flush=True)
