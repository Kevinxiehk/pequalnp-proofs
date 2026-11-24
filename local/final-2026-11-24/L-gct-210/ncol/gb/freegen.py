# Exact (mod p) test of (CC3): column-centred 3x5 level spaces of dim 4 with defect dimension <= 1.  Coordinates (a, beta) in C^5 x C^5
# (NOTES-ncol R2.5; formulas checked numerically): P_2 = 3(sum a beta - A B), P_3 = 6(e3(a) + e3(beta)), deletion of column j:
# d2_j = sum_{k!=j} a_k beta_k - (A - a_j)(B - beta_j),  d3_j = e3(a^(j)) + e3(beta^(j)).   System: F2 == 0, F3 == 0, d2 and d3 parallel
# to m (m in 1^perp of C^5, projective) identically on S in Gr(4,10).  Charts: 210 Pluecker charts x 4 charts m_k = 1 (k = 0..3).
# usage: python3 -I cc3gen.py P OUTDIR [D]     (D = 4 target; D = 3 calibration: (3,<=1) spaces)
import sys, itertools, os
P=int(sys.argv[1]); OUT=sys.argv[2]; D=int(sys.argv[3]) if len(sys.argv)>3 else 4
FREE=(len(sys.argv)>4 and sys.argv[4]=='free')
os.makedirs(OUT,exist_ok=True)
NM=D*(10-D); NV=D+NM+3
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
def e3(v):
    s={}
    for i,j,k in itertools.combinations(range(len(v)),3): s=padd(s,pmul(pmul(v[i],v[j]),v[k]))
    return s
def ssum(v):
    s={}
    for x in v: s=padd(s,x)
    return s
def gen(piv,mk):
    co=[None]*10; mi=0
    for t,c in enumerate(piv): co[c]=var(t)
    for c in range(10):
        if c in piv: continue
        s={}
        for t in range(D): s=padd(s,pmul(var(t),var(D+mi))); mi+=1
        co[c]=s
    a=co[:5]; b=co[5:]
    others=[k for k in range(4) if k!=mk]
    m=[None]*5; m[mk]=ONE
    for t,k in enumerate(others): m[k]=var(D+NM+t)
    m[4]=psc(padd(ONE,ssum([m[k] for k in others])),P-1)
    A=ssum(a); B=ssum(b)
    ab=[pmul(a[j],b[j]) for j in range(5)]
    F2=padd(ssum(ab),psc(pmul(A,B),P-1)); F3=padd(e3(a),e3(b))
    d2=[];d3=[]
    for j in range(5):
        Aj=padd(A,psc(a[j],P-1)); Bj=padd(B,psc(b[j],P-1))
        d2.append(padd(ssum([ab[k] for k in range(5) if k!=j]),psc(pmul(Aj,Bj),P-1)))
        d3.append(padd(e3([a[k] for k in range(5) if k!=j]),e3([b[k] for k in range(5) if k!=j])))
    eqs=[F2,F3]
    for v in (() if FREE else (d2,d3)):
        for j in range(5):
            if j==mk: continue
            eqs.append(padd(v[j],psc(pmul(v[mk],m[j]),P-1)))
    polys=[]
    for E in eqs:
        grp={}
        for k,v in E.items():
            d=grp.setdefault(k[:D],{}); d[k[D:]]=(d.get(k[D:],0)+v)%P
        for d in grp.values():
            terms=[]
            for mon,v in d.items():
                if not v: continue
                mono='*'.join(('x%d^%d'%(i,e) if e>1 else 'x%d'%i) for i,e in enumerate(mon) if e)
                terms.append(str(v)+('*'+mono if mono else ''))
            if terms: polys.append('+'.join(terms))
    return polys
names=','.join('x%d'%i for i in range(NM+(0 if FREE else 3)))
n=0
for piv in itertools.combinations(range(10),D):
    for mk in (range(1) if FREE else range(4)):
        polys=gen(list(piv),mk)
        with open(os.path.join(OUT,('free%d_%s.ms'%(D,''.join(map(str,piv))) if FREE else 'cc3d%d_%s_m%d.ms'%(D,''.join(map(str,piv)),mk))),'w') as f:
            f.write(names+'\n%d\n'%P+',\n'.join(polys)+'\n')
        n+=1
print('wrote',n,'charts to',OUT)
