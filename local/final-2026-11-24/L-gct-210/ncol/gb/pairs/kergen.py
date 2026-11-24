# pair system of chart (pa,pb) + "a random 4x4 combination M of the 12 defect generators has a kernel vector h" (h in chart h_k = 1),
# optionally + Rabinowitsch 1 - z*t_a (and 1 - w*t_b) to exclude same-node points.  Char-p statement only.
# usage: python3 -I kergen.py P PA PB SEED HK RABA RABB OUT.ms     (RABA/RABB = variable index or -1)
import sympy as sp, itertools, sys, random
P=int(sys.argv[1]); pa=[int(c) for c in sys.argv[2]]; pb=[int(c) for c in sys.argv[3]]; random.seed(int(sys.argv[4]))
hk=int(sys.argv[5]); ra=int(sys.argv[6]); rb=int(sys.argv[7]); out=sys.argv[8]
t=sp.symbols('t0:12'); hv=sp.symbols('h0:3'); z,w=sp.symbols('z w'); x1,x2=sp.symbols('x1 x2')
def plane(piv,ts):
    non=[c for c in range(5) if c not in piv]; u=[[0]*5,[0]*5]
    for r in range(2):
        u[r][piv[r]]=1
        for k,c in enumerate(non): u[r][c]=ts[r*3+k]
    return u
ua=plane(pa,t[:6]); vb=plane(pb,t[6:])
def e2(v): return sum(v[i]*v[j] for i,j in itertools.combinations(range(5),2))
def e3(v): return sum(v[i]*v[j]*v[k] for i,j,k in itertools.combinations(range(5),3))
def d2(a,b): A=sum(a); B=sum(b); return [A*b[j]+B*a[j]-2*a[j]*b[j] for j in range(5)]
def d3(a):
    A=sum(a); E=e2(a); return [-a[j]*(E-A*a[j]+a[j]**2) for j in range(5)]
gens=[d2(ua[k],vb[l]) for k in range(2) for l in range(2)]
for U in (ua,vb):
    a=[x1*U[0][j]+x2*U[1][j] for j in range(5)]
    D=[sp.Poly(sp.expand(e),x1,x2) for e in d3(a)]
    for mon in [(3,0),(2,1),(1,2),(0,3)]:
        gens.append([Dj.coeff_monomial(x1**mon[0]*x2**mon[1]) for Dj in D])
R=[[random.randrange(1,1000) for _ in range(12)] for _ in range(4)]
h=[None]*4; it=iter(hv)
for k in range(4): h[k]=1 if k==hk else next(it)
eqs=[]
for U in (ua,vb):
    a=[x1*U[0][j]+x2*U[1][j] for j in range(5)]
    eqs+=sp.Poly(sp.expand(e3(a)),x1,x2).coeffs()
B=lambda a,b: sum(a[j]*b[j] for j in range(5))-sum(a)*sum(b)
eqs+=[sp.expand(B(ua[k],vb[l])) for k in range(2) for l in range(2)]
for r in range(4):
    eqs.append(sp.expand(sum(sum(R[r][g]*gens[g][j] for g in range(12))*h[j] for j in range(4))))
allv=list(t)+list(hv)
if ra>=0: eqs.append(1-z*t[ra]); allv.append(z)
if rb>=0: eqs.append(1-w*t[rb]); allv.append(w)
def ms(e):
    pol=sp.Poly(e,*allv); terms=[]
    for mon,cf in pol.terms():
        v=int(cf)%P
        if v==0: continue
        mono='*'.join(('%s^%d'%(allv[i],k) if k>1 else str(allv[i])) for i,k in enumerate(mon) if k)
        terms.append(str(v)+('*'+mono if mono else ''))
    return '+'.join(terms) if terms else '0'
open(out,'w').write(','.join(str(v) for v in allv)+'\n%d\n'%P+',\n'.join(ms(e) for e in eqs if sp.expand(e)!=0)+'\n')
