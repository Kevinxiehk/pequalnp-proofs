# verify2 r8: exact completeness check of stage3's (M4) classification (F4b twisted free column, s = 1).
# Fat columns are O = (1,1,1,1) or D_{r,r'}(al,be) (exactly two nonzero coordinates); f = #fat <= 3 (>= 2 thin columns).
# Thin columns contribute prod_r (1 + tau_r t_r). Condition: Pi = Q * S = 1 + sum t_r (mod squares).  Unknowns al,be (nonzero), tau_r.
# Extra constraint: at most (5-f) rows have tau_r != 0 (each needs its own thin column).
import itertools, sympy as sp
t=sp.symbols('t0:4'); R=range(4)
def red(e):   # reduce mod t_r^2
    P=sp.Poly(sp.expand(e),*t); out=0
    for mon,c in P.terms():
        if max(mon)<=1: out+=c*sp.prod([t[i]**mon[i] for i in R])
    return sp.expand(out)
pairs=list(itertools.combinations(R,2)); types=['O']+pairs
sols={}
for f in range(0,4):
    for conf in itertools.combinations_with_replacement(range(len(types)),f):
        vs=[]; vars_=[]; nz=[]
        for k,ti in enumerate(conf):
            if types[ti]=='O': vs.append([1,1,1,1])
            else:
                a,b=sp.symbols('al%d be%d'%(k,k)); r,rr=types[ti]; v=[0]*4; v[r]=a; v[rr]=b; vs.append(v); vars_+=[a,b]; nz+=[a,b]
        tau=sp.symbols('tau0:4'); vars_+=list(tau)
        Q=1
        for v in vs: Q=red(Q*(1+sum(v[r]*t[r] for r in R)))
        S=1
        for r in R: S=red(S*(1+tau[r]*t[r]))
        E=sp.Poly(red(Q*S)-(1+sum(t)),*t)
        eqs=[c for mon,c in E.terms()]
        u=sp.Symbol('u'); eqs2=eqs+[u*sp.prod(nz)-1] if nz else eqs
        G=sp.groebner(eqs2,*(vars_+([u] if nz else [])),order='grevlex')
        if list(G.exprs)==[1]: continue
        sols[(f,tuple(types[i] for i in conf))]=G
for k,G in sols.items():
    print(k,'  GB:',[str(g) for g in G.exprs][:12])
