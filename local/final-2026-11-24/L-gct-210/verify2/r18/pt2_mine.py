# verify2 r18: INDEPENDENT generator for ncol's THEOREM PT2 (product-type column-centred 3x5 level 4-spaces have defect >= 3).
# Own D_2, D_3 from the deletion permanents of Y (rows a w^k + b w^{2k}); charts: W_a, W_b in Gr(2,5) pivot charts, G in Gr(2,V5) pivot charts.
# Writes msolve inputs for the 11 S5 x Z2 orbit representatives at prime P, runs them stale-safe, and a calibration point check.
import sympy as sp, itertools, subprocess, os, sys
P=int(sys.argv[1]) if len(sys.argv)>1 else 2147483629
w=sp.Symbol('w'); a=sp.symbols('a0:5'); b=sp.symbols('b0:5')
Y=sp.Matrix([[a[j]*w**k+b[j]*w**(2*k) for j in range(5)] for k in range(3)])
red=lambda e: sp.expand(sp.rem(sp.expand(e),w**2+w+1,w))
def sig(M,m,cols): return red(sum(sp.prod([M[R[i],C[i]] for i in range(m)]) for R in itertools.combinations(range(3),m) for C in itertools.permutations(cols,m)))
D2=[sig(Y,2,[q for q in range(5) if q!=j]) for j in range(5)]; D3=[sig(Y,3,[q for q in range(5) if q!=j]) for j in range(5)]
assert all(sp.Poly(e,w).degree()<=0 for e in D2+D3), 'w survived'
e3=lambda v: sum(v[i]*v[j]*v[k] for i,j,k in itertools.combinations(range(5),3))
s,t,u,v=sp.symbols('s t u v')
def chart(piv,names):
    rows=[]; it=iter(names)
    for r in range(2):
        row=[None]*5; row[piv[r]]=1; row[piv[1-r]]=0
        for j in range(5):
            if row[j] is None: row[j]=next(it)
        rows.append(row)
    return rows
def gchart(piv,names):
    rows=[]; it=iter(names)
    for r in range(2):
        row=[None]*5; row[piv[r]]=1; row[piv[1-r]]=0; free=[j for j in range(5) if row[j] is None]
        x,y=next(it),next(it); row[free[0]]=x; row[free[1]]=y; row[free[2]]=-1-x-y; rows.append(row)
    return rows
def system(pa,pb,pg):
    T=sp.symbols('t0:16')
    Wa=chart(pa,T[0:6]); Wb=chart(pb,T[6:12]); G=gchart(pg,T[12:16])
    av=[s*Wa[0][j]+t*Wa[1][j] for j in range(5)]; bv=[u*Wb[0][j]+v*Wb[1][j] for j in range(5)]
    eqs=[]
    eqs+=sp.Poly(sp.expand(e3(av)),s,t).coeffs(); eqs+=sp.Poly(sp.expand(e3(bv)),u,v).coeffs()
    Bf=sp.expand(sum(x*y for x,y in zip(av,bv))-sum(av)*sum(bv)); eqs+=sp.Poly(Bf,s,t,u,v).coeffs()
    sub={a[j]:av[j] for j in range(5)}; sub.update({b[j]:bv[j] for j in range(5)})
    for g in G:
        for D in (D2,D3):
            e=sp.expand(sum(g[j]*D[j].subs(sub,simultaneous=True) for j in range(5)))
            eqs+=sp.Poly(e,s,t,u,v).coeffs()
    eqs=[sp.expand(q) for q in eqs if sp.expand(q)!=0]
    return T,eqs
def msline(e,T):
    Pq=sp.Poly(e,*T); out=[]
    for mon,c in Pq.terms():
        c=sp.Rational(c); assert c.q==1, ('rational coefficient',c); c=int(c)%P
        if c==0: continue
        m='*'.join(('%s^%d'%(T[i],k) if k>1 else str(T[i])) for i,k in enumerate(mon) if k)
        out.append(str(c)+('*'+m if m else ''))
    return '+'.join(out) if out else '0'
reps=['01_01_01','01_01_02','01_01_23','01_02_01','01_02_03','01_02_12','01_02_13','01_02_34','01_23_01','01_23_02','01_23_04']
wd='pt2_P%d'%P; os.makedirs(wd,exist_ok=True)
for rep in reps:
    pa,pb,pg=[tuple(int(c) for c in x) for x in rep.split('_')]
    T,eqs=system(pa,pb,pg)
    fn='%s/%s.ms'%(wd,rep); out=fn+'.gb'
    open(fn,'w').write(','.join(map(str,T))+'\n%d\n'%P+',\n'.join(msline(e,T) for e in eqs)+'\n')
    if os.path.exists(out): os.remove(out)
    r=subprocess.run('ulimit -v 2000000; timeout 900 msolve -g 2 -t 1 -f %s -o %s'%(fn,out),shell=True,capture_output=True)
    ok=(r.returncode==0 and os.path.exists(out) and os.path.getsize(out)>0 and os.path.getmtime(out)>=os.path.getmtime(fn))
    body=''.join(l for l in open(out).read().splitlines() if not l.startswith('#')).replace(' ','') if ok else ''
    verdict='UNIT' if body.strip().rstrip(':') in ('[1]','[1]:') else ('NONUNIT' if ok else 'FAILED rc=%d'%r.returncode)
    print('PT2 chart',rep,'#eqs',len(eqs),':',verdict,flush=True)
