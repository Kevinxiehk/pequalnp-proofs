# local multiplicities at the same-node points (mod p): of Y (pair ideal) and of Y + det(M) (same random M as mkq.py with the same seed),
# computed in the local ring (ds) with Laplace expansion reduced modulo the local standard basis.  usage: python3 -I mkloc3.py P CHART SEED OUTDIR
import sympy as sp, itertools, sys, random, os
P=int(sys.argv[1]); chart=sys.argv[2]; random.seed(int(sys.argv[3])); od=sys.argv[4]; os.makedirs(od,exist_ok=True)
pa=[int(c) for c in chart.split('_')[0]]; pb=[int(c) for c in chart.split('_')[1]]
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
gens=[d2(ua[k],vb[l]) for k in range(2) for l in range(2)]; eqs=[]
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
I_=next(c for a in range(2,10**6) for c in [pow(a,(P-1)//4,P)] if c*c%P==P-1)
roots={'i':I_,'-1':P-1,'-i':P-I_}; pts=[]
for perm in itertools.permutations(['i','-1','-i']):
    v=[roots[x] for x in perm]
    if chart=='01_01':
        pts.append(('n0_'+'_'.join(perm),[0,0,0]+v+[0,0,0]+v)); pts.append(('n1_'+'_'.join(perm),v+[0,0,0]+v+[0,0,0]))
    elif chart=='01_02':
        c=[0,1]+v; inv=pow(c[2],P-2,P); w=[x*inv%P for x in c]
        pts.append(('n0_'+'_'.join(perm),[0,0,0]+v+[0,0,0]+[w[1],w[3],w[4]]))
for name,pt in pts:
    L=['ring Rg = %d, (%s), dp;'%(P,','.join(str(v) for v in t)),'ideal I = %s;'%(','.join(S(e) for e in eqs)),'matrix M[4][4];']
    for r in range(4):
        for j in range(4): L.append('M[%d,%d] = %s;'%(r+1,j+1,S(sum(R[r][g]*gens[g][j] for g in range(12)))))
    L+=['ring Rl = %d, (%s), ds;'%(P,','.join(str(v) for v in t)),'map f = Rg, %s;'%(','.join('t%d+(%d)'%(k,pt[k]) for k in range(12))),
        'ideal G = std(f(I)); matrix N = f(M);','"LOC %s Y", vdim(G);'%name,
        '''proc det2(poly a, poly b, poly c, poly d, ideal G){ return(reduce(a*d-b*c,G)); }
int i; int j; int k; poly Dt = 0;
for(i=1;i<=4;i++){ for(j=i+1;j<=4;j++){
  poly m12 = det2(N[1,i],N[1,j],N[2,i],N[2,j],G);
  intvec rest; int c=0; for(k=1;k<=4;k++){ if(k!=i && k!=j){ c++; rest[c]=k; } }
  poly m34 = det2(N[3,rest[1]],N[3,rest[2]],N[4,rest[1]],N[4,rest[2]],G);
  int sgn = (-1)^(i+j+1+2);
  Dt = Dt + sgn*reduce(m12*m34,G);
  kill rest; kill c; kill m12; kill m34; kill sgn;
}}''','"LOC %s Y+D", vdim(std(G+ideal(reduce(Dt,G))));'%name,'quit;']
    open(os.path.join(od,'%s_%s.sing'%(chart,name)),'w').write('\n'.join(L)+'\n')
print(len(pts))
