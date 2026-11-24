# PRODUCT-TYPE column-centred 3x5 level 4-spaces S = W_a (+) W_b with defect inside an E-dim subspace D of V5 (NOTES-ncol R3.3/R3.4).
# Unknowns: W_a, W_b in Gr(2,5) charts (6 + 6), complement of D in V5^* = C^5/C1: (4-E) vectors g_k in a Gr(4-E,4) chart.
# Equations (coefficients in x, y): e3 == 0 on W_a and on W_b; a.b - A B == 0; g_k . d2(a,b) == 0; g_k . d3a(a) == 0; g_k . d3b(b) == 0,
# d2 = A b + B a - 2 a o b, d3a_j = -a_j (e2(a) - A a_j + a_j^2).   usage: python3 -I prodgen.py P E OUTDIR
import sys, itertools, os
P=int(sys.argv[1]); E=int(sys.argv[2]); OUT=sys.argv[3]; os.makedirs(OUT,exist_ok=True)
K=2; NG=4
NV=4+12+NG     # x1,x2,y1,y2, W_a(6), W_b(6), g
def padd(a,b):
    c=dict(a)
    for k,v in b.items():
        w=(c.get(k,0)+v)%P
        if w: c[k]=w
        else: c.pop(k,None)
    return c
def pmul(a,b):
    c={}
    for k1,v1 in a.items():
        for k2,v2 in b.items():
            k=tuple(x+y for x,y in zip(k1,k2)); w=(c.get(k,0)+v1*v2)%P
            if w: c[k]=w
            else: c.pop(k,None)
    return c
def psc(a,s): return {k:(v*s)%P for k,v in a.items() if (v*s)%P}
def var(i):
    e=[0]*NV; e[i]=1; return {tuple(e):1}
ONE={tuple([0]*NV):1}
def ssum(v):
    s={}
    for x in v: s=padd(s,x)
    return s
def plane(piv,off,coef):
    # basis u1,u2 of a 2-plane in C^5 in chart piv=(p,q); returns vector a(x) = coef[0]*u1 + coef[1]*u2 as 5 polys
    non=[c for c in range(5) if c not in piv]; u=[[None]*5 for _ in range(2)]
    for r in range(2):
        for c in range(5):
            if c==piv[r]: u[r][c]=ONE
            elif c in piv: u[r][c]={}
            else: u[r][c]=var(off+r*3+non.index(c))
    return [padd(pmul(coef[0],u[0][c]),pmul(coef[1],u[1][c])) for c in range(5)]
def e2(v):
    s={}
    for i,j in itertools.combinations(range(5),2): s=padd(s,pmul(v[i],v[j]))
    return s
def e3(v):
    s={}
    for i,j,k in itertools.combinations(range(5),3): s=padd(s,pmul(pmul(v[i],v[j]),v[k]))
    return s
def d3(v):
    A=ssum(v); E2=e2(v)
    return [psc(pmul(v[j],padd(padd(E2,psc(pmul(A,v[j]),P-1)),pmul(v[j],v[j]))),P-1) for j in range(5)]
def gvecs(gpiv):
    # E = 2: G = 2-dim subspace of V5 (sum-zero vectors), chart: g_r[gpiv[r]] = 1, g_r[gpiv[1-r]] = 0, the other three coordinates
    # c1 < c2 < c3 with c1, c2 free and c3 fixed by the sum-zero condition.
    non=[c for c in range(5) if c not in gpiv]; G=[]
    for r in range(2):
        g=[None]*5
        g[gpiv[r]]=ONE; g[gpiv[1-r]]={}
        g[non[0]]=var(16+2*r); g[non[1]]=var(17+2*r)
        g[non[2]]=psc(padd(padd(ONE,var(16+2*r)),var(17+2*r)),P-1)
        G.append(g)
    return G
def dot(g,v):
    s={}
    for c in range(5): s=padd(s,pmul(g[c],v[c]))
    return s
X=[var(0),var(1)]; Yv=[var(2),var(3)]
names=','.join('t%d'%i for i in range(12)); n=0
REPS=set(l.strip() for l in open(sys.argv[4]).read().split())
ONLY=sys.argv[5] if len(sys.argv)>5 else 'all'
for pa in itertools.combinations(range(5),2):
    for pb in itertools.combinations(range(5),2):
        for gp in [(0,1)]:
            tag='%s_%s'%(''.join(map(str,pa)),''.join(map(str,pb)))
            if tag not in REPS: continue
            a=plane(pa,4,X); b=plane(pb,10,Yv); G=gvecs(gp)
            A=ssum(a); B=ssum(b)
            d2=[padd(padd(pmul(A,b[j]),pmul(B,a[j])),psc(pmul(a[j],b[j]),P-2)) for j in range(5)]
            F2=padd(ssum([pmul(a[j],b[j]) for j in range(5)]),psc(pmul(A,B),P-1))
            eqs=[e3(a),e3(b),F2]
            polys=[]
            for Eq in eqs:
                grp={}
                for k,v in Eq.items():
                    d=grp.setdefault(k[:4],{}); d[k[4:]]=(d.get(k[4:],0)+v)%P
                for d in grp.values():
                    terms=[]
                    for mon,v in d.items():
                        if not v: continue
                        mono='*'.join(('t%d^%d'%(i,e) if e>1 else 't%d'%i) for i,e in enumerate(mon) if e)
                        terms.append(str(v)+('*'+mono if mono else ''))
                    if terms: polys.append('+'.join(terms))
            fn=os.path.join(OUT,'pair_%s.ms'%tag)
            open(fn,'w').write(names+'\n%d\n'%P+',\n'.join(polys)+'\n'); n+=1
print('wrote',n,'charts')
