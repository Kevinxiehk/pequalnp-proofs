# verify2 r9: q-at-all-base-points extension test for the WHOLE D04-PROP family alpha = (1,1,-1,-1), sg symbolic (Singular over Q).
# polynomials: dict {(x0..x4, sg) exponents: int}; equations in (c..., sg) = x-coefficients.  usage: python3 -I ext_qsym.py K [timeout=T]
import sys, json, itertools, subprocess, time, os, sympy as sp
K=int(sys.argv[1]); opts=dict(a.split('=') for a in sys.argv[2:] if '=' in a); TMO=float(opts.get('timeout',600))
D=json.load(open('/home/kevxhk/work/L-gct-210/verify2/r8/ext_T1_sym.json')); sgS=sp.Symbol('sg')
def topoly(e):   # sympy expr in sg -> {sg power: int}
    p=sp.Poly(sp.sympify(e),sgS); return {m[0]:int(c) for m,c in p.terms()} if sp.sympify(e)!=0 else {}
X=[[topoly(e) for e in x] for x in D['X']]; U=[[topoly(e) for e in u] for u in D['U']]; n=len(U)
NV=6  # x0..x4, sg
def padd(a,b,c=1):
    r=dict(a)
    for k,v in b.items():
        x=r.get(k,0)+c*v
        if x: r[k]=x
        elif k in r: del r[k]
    return r
def pmul(a,b):
    r={}
    for k1,v1 in a.items():
        for k2,v2 in b.items():
            k=tuple(x+y for x,y in zip(k1,k2)); r[k]=r.get(k,0)+v1*v2
    return {k:v for k,v in r.items() if v}
def sgp(d,shift=None):  # {sg power: c} -> poly in NV vars, optional x-variable factor
    out={}
    for pw,c in d.items():
        k=[0]*NV; k[5]=pw
        if shift is not None: k[shift]+=1
        out[tuple(k)]=out.get(tuple(k),0)+c
    return out
Z0=tuple([0]*NV)
E=[[padd({Z0:1},{}) for b in range(5)] for a in range(5)]
for a in range(5):
    for b in range(5):
        for q in range(5):
            if X[q][a*5+b]: E[a][b]=padd(E[a][b],sgp(X[q][a*5+b],q))
def perm3(rows,cols):
    tot={}
    for s in itertools.permutations(range(3)):
        t={Z0:1}
        for i in range(3): t=pmul(t,E[rows[i]][cols[s[i]]])
        tot=padd(tot,t)
    return tot
H={}
for (a,b),(c,d) in itertools.product(itertools.product(range(5),range(5)),repeat=2):
    if a!=c and b!=d and (a*5+b)<=(c*5+d):
        H[(a*5+b,c*5+d)]=perm3([r for r in range(5) if r not in (a,c)],[r for r in range(5) if r not in (b,d)])
def Hget(i,j): return H[(i,j)] if i<=j else H[(j,i)]
Q={}
for A in range(n):
    for B in range(A,n):
        tot={}
        for i in range(25):
            if not U[A][i]: continue
            for j in range(25):
                if not U[B][j]: continue
                if (i,j) in H or (j,i) in H: tot=padd(tot,pmul(pmul(sgp(U[A][i]),sgp(U[B][j])),Hget(i,j)))
        Q[(A,B)]=tot
def Qget(A,B): return Q[(A,B)] if A<=B else Q[(B,A)]
CL=list(itertools.combinations(range(n),K)); res={}; t0=time.time()
SEL=set(range(len(CL))) if opts.get('cells','all')=='all' else set(int(c) for c in opts['cells'].split(','))
OUT='/home/kevxhk/work/L-gct-210/verify2/r8/extqS'; os.makedirs(OUT,exist_ok=True)
for ci,piv in enumerate(CL):
    if ci not in SEL: continue
    free=[(i,j) for i in range(K) for j in range(n) if j>piv[i] and j not in piv]; nc=len(free); cidx={f:t for t,f in enumerate(free)}
    def coeff(i,A):
        if A==piv[i]: return {tuple([0]*nc):1}
        if (i,A) in cidx: k=[0]*nc; k[cidx[(i,A)]]=1; return {tuple(k):1}
        return {}
    eqs=[]
    for i in range(K):
        for j in range(i,K):
            byx={}
            for A in range(n):
                ca=coeff(i,A)
                if not ca: continue
                for B in range(n):
                    cb=coeff(j,B)
                    if not cb: continue
                    cc=pmul(ca,cb)
                    for k,v in Qget(A,B).items():
                        xm=k[:5]; sgpow=k[5]
                        add={kk+(sgpow,):w*v for kk,w in cc.items()}
                        byx[xm]=padd(byx.get(xm,{}),add)
            eqs+=[p for p in byx.values() if p]
    names=['c%d'%t for t in range(nc)]+['sg']
    def fmt(p):
        ts=[]
        for k,v in p.items():
            m='*'.join('%s^%d'%(names[t],e) for t,e in enumerate(k) if e)
            ts.append('(%d)*%s'%(v,m) if m else '(%d)'%v)
        return '+'.join(ts)
    fn='%s/D04Psym_k%d_cell%03d.sing'%(OUT,K,ci)
    with open(fn,'w') as f:
        f.write('ring r=0,(%s),dp;\nideal I=%s;\nideal G=std(I);\nif (size(G)==1 and G[1]==1) {"RES UNIT";} else {"RES NONUNIT",dim(G); ideal EL=eliminate(G,%s); "ELIM"; EL;}\nquit;\n'%(','.join(names),',\n'.join(fmt(p) for p in eqs),'*'.join(names[:-1]) if nc else '1'))
    try:
        o=subprocess.run(['/usr/bin/Singular','-q',fn],capture_output=True,text=True,timeout=TMO).stdout
        r=[l for l in o.splitlines() if l.startswith('RES')]; res[ci]=r[0] if r else 'ERROR'
        if 'NONUNIT' in res[ci]: res[ci]+=' | '+' '.join(o.split('ELIM')[1].split())[:200] if 'ELIM' in o else ''
    except subprocess.TimeoutExpired: res[ci]='TIMEOUT'
    print(ci,piv,'nvars',nc+1,'neqs',len(eqs),res[ci],'%.0fs'%(time.time()-t0),flush=True)
v=list(res.values())
print('SUMMARY D04Psym k=%d: cells %d, UNIT %d, other %d'%(K,len(v),sum(x=='RES UNIT' for x in v),sum(x!='RES UNIT' for x in v)),flush=True)
