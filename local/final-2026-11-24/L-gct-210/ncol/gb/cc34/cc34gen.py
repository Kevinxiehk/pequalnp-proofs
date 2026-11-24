# column-centred 3x4 level spaces of dim D: in isotropic coordinates (a, beta) in C^4 x C^4: P_2 = 3(sum a beta - A B), P_3 = 6(e3(a)+e3(beta)).
# Gr(D,8) Pluecker charts, orbit representatives under S4 x Z2.   usage: python3 -I cc34gen.py P D OUTDIR
import sys, itertools, os
P=int(sys.argv[1]); D=int(sys.argv[2]); OUT=sys.argv[3]; os.makedirs(OUT,exist_ok=True)
NM=D*(8-D); NV=D+NM
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
def ssum(v):
    s={}
    for x in v: s=padd(s,x)
    return s
def e3(v):
    s={}
    for i,j,k in itertools.combinations(range(len(v)),3): s=padd(s,pmul(pmul(v[i],v[j]),v[k]))
    return s
seen=set(); reps=[]
for Pv in itertools.combinations(range(8),D):
    best=min(tuple(sorted(perm[c%4]+(4 if (c>=4)^sw else 0) for c in Pv)) for perm in itertools.permutations(range(4)) for sw in (0,1))
    if best not in seen: seen.add(best); reps.append(best)
names=','.join('x%d'%i for i in range(NM))
for piv in reps:
    co=[None]*8; mi=0
    for t,c in enumerate(piv): co[c]=var(t)
    for c in range(8):
        if c in piv: continue
        s={}
        for t in range(D): s=padd(s,pmul(var(t),var(D+mi))); mi+=1
        co[c]=s
    a=co[:4]; b=co[4:]
    F2=padd(ssum([pmul(a[j],b[j]) for j in range(4)]),psc(pmul(ssum(a),ssum(b)),P-1)); F3=padd(e3(a),e3(b))
    polys=[]
    for E in (F2,F3):
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
    open(os.path.join(OUT,'c34_%s.ms'%''.join(map(str,piv))),'w').write(names+'\n%d\n'%P+',\n'.join(polys)+'\n')
print(len(reps),'orbit charts:',reps)
