# Singular script: pair ideal of chart (pa,pb) mod p, its standard basis G (dp), vdim, then D = det(M) for a random 4x4 combination M of the
# 12 defect generators, and vdim(std(G + D)).  usage: python3 -I mksing.py P PA PB SEED OUT.sing
import sympy as sp, itertools, sys, random
P=int(sys.argv[1]); pa=[int(c) for c in sys.argv[2]]; pb=[int(c) for c in sys.argv[3]]; random.seed(int(sys.argv[4])); out=sys.argv[5]
t=sp.symbols('t0:12'); x1,x2=sp.symbols('x1 x2')
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
eqs=[]
for U in (ua,vb):
    a=[x1*U[0][j]+x2*U[1][j] for j in range(5)]
    D=[sp.Poly(sp.expand(e),x1,x2) for e in d3(a)]
    for mon in [(3,0),(2,1),(1,2),(0,3)]:
        gens.append([Dj.coeff_monomial(x1**mon[0]*x2**mon[1]) for Dj in D])
    eqs+=sp.Poly(sp.expand(e3(a)),x1,x2).coeffs()
B=lambda a,b: sum(a[j]*b[j] for j in range(5))-sum(a)*sum(b)
eqs+=[sp.expand(B(ua[k],vb[l])) for k in range(2) for l in range(2)]
R=[[random.randrange(1,1000) for _ in range(12)] for _ in range(4)]
def S(e): return str(sp.expand(e)).replace('**','^')
L=['ring Rg = %d, (%s), dp;'%(P,','.join(str(v) for v in t)),'option(redSB);']
L.append('ideal I = %s;'%(','.join(S(e) for e in eqs)))
L+=['ideal G = std(I);','"VDIM_I", vdim(G);']
L.append('matrix M[4][4];')
for r in range(4):
    for j in range(4):
        L.append('M[%d,%d] = %s;'%(r+1,j+1,S(sum(R[r][g]*gens[g][j] for g in range(12)))))
L+=['poly D = reduce(det(M),G);','ideal H = std(G+ideal(D));','"VDIM_I_PLUS_DET", vdim(H);','quit;']
open(out,'w').write('\n'.join(L)+'\n')
