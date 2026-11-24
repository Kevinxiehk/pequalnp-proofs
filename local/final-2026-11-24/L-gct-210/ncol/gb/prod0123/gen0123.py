# (PROD) chart 0123 of Gr(4,10) with the isotropy eliminated exactly:  S = {(F t, G t)}, F = [I_4 ; f^T], H := (I - J) G = [K - f h^T ; h^T]
# with K 4x4 skew, h in C^4; G = (I - J/4) H.  (F^T (I-J) G = F^T H = K - f h^T + f h^T = K: skew.)  This is a bijective reparametrisation of the
# Pluecker chart 0123 intersected with the isotropy locus, so it is the same chart of the projective system.  Equations: coefficients of
# e_3(F t) + e_3(G t) in t (20).  Unknowns f (4), K (6), h (4).   usage: python3 -I gen0123.py P OUT.ms
import sympy as sp, itertools, sys
P=int(sys.argv[1]); out=sys.argv[2]
t=sp.symbols('t0:4'); f=sp.symbols('f0:4'); kk=sp.symbols('k0:6'); h=sp.symbols('h0:4')
K=sp.zeros(4,4); idx=0
for i in range(4):
    for j in range(i+1,4): K[i,j]=kk[idx]; K[j,i]=-kk[idx]; idx+=1
F=sp.Matrix.vstack(sp.eye(4), sp.Matrix([list(f)]))
H=sp.Matrix.vstack(K-sp.Matrix(f)*sp.Matrix([list(h)]), sp.Matrix([list(h)]))
J5=sp.ones(5,5); G=(sp.eye(5)-J5/4)*H
tv=sp.Matrix(t); a=list(F*tv); b=list(G*tv)
# check isotropy symbolically
iso=sp.expand((sp.Matrix(a).T*(sp.eye(5)-J5)*sp.Matrix(b))[0]); assert iso==0, iso
def e3(v): return sum(v[i]*v[j]*v[l] for i,j,l in itertools.combinations(range(5),3))
Fp=sp.expand(e3(a)+e3(b))
unk=list(f)+list(kk)+list(h)
lines=[]
for c in sp.Poly(Fp,*t).coeffs():
    pol=sp.Poly(sp.expand(c),*unk); terms=[]
    for mon,cf in pol.terms():
        cf=sp.Rational(cf); v=(int(cf.p)%P)*pow(int(cf.q)%P,P-2,P)%P
        if v==0: continue
        mono='*'.join(('%s^%d'%(u,e) if e>1 else str(u)) for u,e in zip(unk,mon) if e)
        terms.append(str(v)+('*'+mono if mono else ''))
    if terms: lines.append('+'.join(terms))
open(out,'w').write(','.join(str(u) for u in unk)+'\n%d\n'%P+',\n'.join(lines)+'\n')
print('wrote',len(lines),'equations; isotropy identity verified')
