# Round 19: EXACT triviality of a one-parameter deformation M(t) = M0 + t D of a family at a fixed base point over Q(w), w^2+w+1 = 0.
# Trivial <=> rank [M0; D] = rank M0 (= 6), computed with DomainMatrix over QQ<sqrt(-3)> (w = (-1+sqrt(-3))/2).  The family must be linear in t.
#   usage: defo_trivial_exact.py FAMILY name=expr ...   (expr in w, e.g. m1=-1-w m2=w)
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
import sympy as sp
from sympy.polys.matrices import DomainMatrix
fam=sys.argv[1]; fixed=dict(a.split('=') for a in sys.argv[2:])
argv0=sys.argv; sys.argv=['x',fam,'16','1','1']
src=open('/home/kevxhk/work/L-gct-210/reg2/gb/gen_rank.py').read(); exec(src[:src.index('F=Family(params,bfn,d)')])
from famtool import Ring
R0=Ring(list(params)); Bs=bfn(R0,R0.var)
syms={n:sp.Symbol(n) for n in params}
r3=sp.sqrt(-3); wv=(-1+r3)/2
sub={syms[n]:sp.sympify(e,locals={'w':sp.Symbol('w')}).subs(sp.Symbol('w'),wv) for n,e in fixed.items()}
if 'w' in syms: sub[syms['w']]=wv
def topoly(q):
    return sum(sp.Integer(v.numerator)/sp.Integer(v.denominator)*sp.Mul(*[syms[params[i]]**e for i,e in enumerate(k)]) if hasattr(v,'numerator') else sp.nsimplify(v)*sp.Mul(*[syms[params[i]]**e for i,e in enumerate(k)]) for k,v in q.items())
t=syms['t']; K=sp.QQ.algebraic_field(r3)
rowsM0=[];rowsD=[]
for B in Bs:
    e0=[];e1=[]
    for i in range(4):
        for j in range(5):
            p=sp.expand(topoly(B[i][j]).subs(sub)) if B[i][j] else sp.Integer(0)
            pt=sp.Poly(p,t) if p!=0 else None
            if pt is not None and pt.degree()>1: raise SystemExit('not linear in t')
            e0.append(pt.coeff_monomial(1) if pt is not None else 0); e1.append(pt.coeff_monomial(t) if pt is not None else 0)
    rowsM0.append(e0); rowsD.append(e1)
conv=lambda rows: DomainMatrix([[K.from_sympy(sp.nsimplify(sp.expand(x))) for x in r] for r in rows],(len(rows),20),K)
r0=conv(rowsM0).rank(); rD=[r for r in rowsD if any(x!=0 for x in r)]; r1=conv(rowsM0+rD).rank() if rD else r0
print('%s %s: rank M0 = %d, rank [M0; D] = %d, nonzero D rows %d  => %s [exact over QQ<sqrt(-3)>]'%(fam,fixed,r0,r1,len(rD),'TRIVIAL' if r1==r0 else 'GENUINE'),flush=True)
