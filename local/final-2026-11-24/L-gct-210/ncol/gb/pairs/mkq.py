# Singular script using msolve's reduced GB (grevlex = dp, same variable order) as a standard basis: quotient-algebra determinant test.
# usage: python3 -I mkq.py P PA PB SEED GBFILE OUT.sing
import sympy as sp, itertools, sys, random, re
P=int(sys.argv[1]); pa=[int(c) for c in sys.argv[2]]; pb=[int(c) for c in sys.argv[3]]; random.seed(int(sys.argv[4])); gbf=sys.argv[5]; out=sys.argv[6]
t=sp.symbols('t0:12'); x1,x2=sp.symbols('x1 x2')
def plane(piv,ts):
    non=[c for c in range(5) if c not in piv]; u=[[0]*5,[0]*5]
    for r in range(2):
        u[r][piv[r]]=1
        for k,c in enumerate(non): u[r][c]=ts[r*3+k]
    return u
ua=plane(pa,t[:6]); vb=plane(pb,t[6:])
def e2(v): return sum(v[i]*v[j] for i,j in itertools.combinations(range(5),2))
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
def S(e): return str(sp.expand(e)).replace('**','^')
gbtxt=open(gbf).read().split('#---')[-1].strip().lstrip('[').rstrip(':').rstrip(']').replace('\n','')
gbtxt=re.sub(r'\^1(?!\d)','',gbtxt)
L=['ring Rg = %d, (%s), dp;'%(P,','.join(str(v) for v in t)),'option(redSB);','ideal G = %s;'%gbtxt,'attrib(G,"isSB",1);','"VDIM_G", vdim(G);']
L.append('matrix M[4][4];')
for r in range(4):
    for j in range(4):
        L.append('M[%d,%d] = reduce(%s,G);'%(r+1,j+1,S(sum(R[r][g]*gens[g][j] for g in range(12)))))
L.append('''proc det2(poly a, poly b, poly c, poly d, ideal G){ return(reduce(a*d-b*c,G)); }
// 4x4 determinant by Laplace expansion on 2x2 minors (rows 1,2 / rows 3,4), reducing modulo G at each step
int i; int j; int k; int l; poly Dt = 0; list cols;
for(i=1;i<=4;i++){ for(j=i+1;j<=4;j++){
  poly m12 = det2(M[1,i],M[1,j],M[2,i],M[2,j],G);
  intvec rest; int c=0; for(k=1;k<=4;k++){ if(k!=i && k!=j){ c++; rest[c]=k; } }
  poly m34 = det2(M[3,rest[1]],M[3,rest[2]],M[4,rest[1]],M[4,rest[2]],G);
  int sgn = (-1)^(i+j+1+2);
  Dt = Dt + sgn*reduce(m12*m34,G);
  kill rest; kill c; kill m12; kill m34; kill sgn;
}}
Dt = reduce(Dt,G);
"DET_IS_ZERO_IN_QUOTIENT", Dt==0;
ideal H = std(G+ideal(Dt));
"VDIM_G_PLUS_DET", vdim(H);
quit;''')
open(out,'w').write('\n'.join(L)+'\n')
