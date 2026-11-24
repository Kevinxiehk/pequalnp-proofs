# Common rank-drop locus of the sampled B_c [NOTES-stage2 R15-4]: from the exact factorisations cof_ii(B_c) (logs of r16_Kfast.py), drop the
# setup-exceptional factors and compute  INTERSECTION over c of  UNION over the remaining factors f of V(f)  (exact, Groebner bases over Q).
import sys, re, itertools, sympy as sp
nu,a1,a2,a3=sp.symbols('nu a1 a2 a3'); loc={'nu':nu,'a1':a1,'a2':a2,'a3':a3}
EXC=[nu,nu+1,3*nu-1,a1+a2+a3-4,a1]          # detX = -4 a1 nu, dens = (nu+1)(3nu-1)(a1+a2+a3-4)
fams=[]
for fn in sys.argv[1:]:
    for l in open(fn):
        m=re.match(r'\s*cof_ii\(B_c\) = (.*)',l)
        if m:
            fl=sp.factor_list(sp.sympify(m.group(1),locals=loc))[1]
            keep=[f for f,e in fl if not any(sp.simplify(f/x).is_number for x in EXC)]
            fams.append(keep); print('c-sample',len(fams),': non-exceptional factors',keep,flush=True)
vars_=[nu,a1,a2,a3]; comps=set()
for choice in itertools.product(*fams):
    G=sp.groebner(list(choice),*vars_,order='lex')
    if list(G)==[1]: continue
    comps.add(tuple(G))
print('nonempty intersections (Groebner bases, lex nu>a1>a2>a3):',flush=True)
for G in sorted(comps,key=str): print('  ',list(G),flush=True)
