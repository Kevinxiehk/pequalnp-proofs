# pair system of chart (pa,pb) PLUS one random 4x4 combination determinant of the 12 defect generators (d2(u_k,v_l), cubic coefficients of
# d3a on W_a and d3b on W_b), in V5 coordinates (first 4 entries).  UNIT  =>  no point of the pair scheme in this chart has defect <= 3 (mod p).
# usage: python3 -I detgen.py P PA PB SEED OUT.ms
import sympy as sp, itertools, sys, random
P=int(sys.argv[1]); pa=[int(c) for c in sys.argv[2]]; pb=[int(c) for c in sys.argv[3]]; random.seed(int(sys.argv[4])); out=sys.argv[5]
t=sp.symbols('t0:12'); x1,x2=sp.symbols('x1 x2')
def plane(piv,ts):
    non=[c for c in range(5) if c not in piv]; u=[[0]*5,[0]*5]
    for r in range(2):
        u[r][piv[r]]=1
        for k,c in enumerate(non): u[r][c]=ts[r*3+k]
    return [sp.Matrix(u[0]),sp.Matrix(u[1])]
ua=plane(pa,t[:6]); vb=plane(pb,t[6:])
def e2(v): return sum(v[i]*v[j] for i,j in itertools.combinations(range(5),2))
def e3(v): return sum(v[i]*v[j]*v[k] for i,j,k in itertools.combinations(range(5),3))
def d2(a,b): A=sum(a); B=sum(b); return [A*b[j]+B*a[j]-2*a[j]*b[j] for j in range(5)]
def d3(a):
    A=sum(a); E=e2(a); return [-a[j]*(E-A*a[j]+a[j]**2) for j in range(5)]
gens=[d2(list(ua[k]),list(vb[l])) for k in range(2) for l in range(2)]
for U in (ua,vb):
    a=[x1*U[0][j]+x2*U[1][j] for j in range(5)]
    D=[sp.Poly(sp.expand(e),x1,x2) for e in d3(a)]
    for mon in [(3,0),(2,1),(1,2),(0,3)]:
        gens.append([Dj.coeff_monomial(x1**mon[0]*x2**mon[1]) for Dj in D])
R=[[random.randrange(1,1000) for _ in range(12)] for _ in range(4)]
M=sp.Matrix([[sum(R[r][g]*gens[g][j] for g in range(12)) for j in range(4)] for r in range(4)])
det=sp.expand(M.det(method='berkowitz'))
# pair equations
eqs=[]
for U in (ua,vb):
    a=[x1*U[0][j]+x2*U[1][j] for j in range(5)]
    eqs+=sp.Poly(sp.expand(e3(a)),x1,x2).coeffs()
B=lambda a,b: sum(a[j]*b[j] for j in range(5))-sum(a)*sum(b)
eqs+=[sp.expand(B(list(ua[k]),list(vb[l]))) for k in range(2) for l in range(2)]
eqs.append(det)
def ms(e):
    pol=sp.Poly(e,*t); terms=[]
    for mon,cf in pol.terms():
        v=int(cf)%P
        if v==0: continue
        mono='*'.join(('t%d^%d'%(i,k) if k>1 else 't%d'%i) for i,k in enumerate(mon) if k)
        terms.append(str(v)+('*'+mono if mono else ''))
    return '+'.join(terms) if terms else '0'
open(out,'w').write(','.join(str(v) for v in t)+'\n%d\n'%P+',\n'.join(ms(e) for e in eqs if sp.expand(e)!=0)+'\n')
print('det terms:',len(sp.Poly(det,*t).terms()))
