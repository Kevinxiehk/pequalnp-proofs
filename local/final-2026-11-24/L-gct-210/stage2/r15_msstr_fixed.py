# Correct msolve writer: clears rational denominators of each polynomial (scaling by a unit), then reduces mod p.
import sympy as sp
NONINT=[0]
def msstr(e,vars_,p):
    p=int(p); P=sp.Poly(sp.expand(e),*vars_)
    dens=[sp.Rational(c).q for c in P.coeffs()]
    L=1
    for d in dens: L=sp.ilcm(L,d)
    if L!=1: NONINT[0]+=1
    if p and L%p==0: raise ValueError('denominator divisible by p')
    terms=[]
    for mon,c in P.terms():
        c=sp.Rational(c)*L; assert c.q==1; c=int(c.p)
        if p: c%=p
        if c==0: continue
        mono='*'.join('%s^%d'%(v,k) if k>1 else str(v) for v,k in zip(vars_,mon) if k>0)
        terms.append(str(c)+('*'+mono if mono else ''))
    return '+'.join(terms) if terms else '0'
