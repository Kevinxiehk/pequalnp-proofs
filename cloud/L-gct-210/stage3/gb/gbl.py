# Round 8 (stage3): small modular polynomial library + msolve interface (pure Python).  Polynomials: dict {exponent tuple: coeff mod P}.
import itertools, subprocess, os
P=65521; NV=0
def setup(p,nv):
    global P,NV; P=p; NV=nv
def const(c): 
    c%=P; return {tuple([0]*NV):c} if c else {}
def var(i):
    e=[0]*NV; e[i]=1; return {tuple(e):1}
def add(a,b,cb=1):
    r=dict(a)
    for k,v in b.items():
        x=(r.get(k,0)+cb*v)%P
        if x: r[k]=x
        elif k in r: del r[k]
    return r
def sub(a,b): return add(a,b,-1)
def scal(c,a):
    c%=P; return {k:v*c%P for k,v in a.items()} if c else {}
def mul(a,b):
    if len(a)>len(b): a,b=b,a
    r={}
    for k1,v1 in a.items():
        for k2,v2 in b.items():
            k=tuple(x+y for x,y in zip(k1,k2)); r[k]=(r.get(k,0)+v1*v2)%P
    return {k:v for k,v in r.items() if v}
def lin(terms):          # sum of (coeff, poly)
    r={}
    for c,a in terms: r=add(r,a,c)
    return r
def perm(M):             # permanent of an n x n matrix of polynomials (DP over column subsets)
    n=len(M); dp={0:const(1)}
    for i in range(n):
        nd={}
        for S,v in dp.items():
            if not v: continue
            for j in range(n):
                if S>>j&1 or not M[i][j]: continue
                T=S|1<<j; t=mul(v,M[i][j]); nd[T]=add(nd[T],t) if T in nd else t
        dp=nd
    return dp.get((1<<n)-1,{})
def subperms(rows,k,ncol):   # rows: list of k vectors (lists of polys, length ncol): dict {column subset: k x k permanent}
    return {S:perm([[r[j] for j in S] for r in rows]) for S in itertools.combinations(range(ncol),k)}
def coeffs(f,params):    # split f by the exponents of the parameter variables: {param exps: poly without params}
    out={}
    for k,v in f.items():
        pk=tuple(k[i] for i in params); rk=tuple(0 if i in params else k[i] for i in range(NV))
        out.setdefault(pk,{})[rk]=v
    return out
def tostr(f,names):
    if not f: return '0'
    ts=[]
    for k,v in sorted(f.items(),reverse=True):
        m='*'.join('%s^%d'%(names[i],e) for i,e in enumerate(k) if e)
        ts.append('%d*%s'%(v,m) if m else '%d'%v)
    return '+'.join(ts)
def write_ms(path,names,polys,use):       # use: indices of the variables that occur (others must not appear)
    polys=[f for f in polys if f]
    for f in polys:
        for k in f: assert all(k[i]==0 for i in range(NV) if i not in use), 'unused variable occurs'
    with open(path,'w') as fh:
        fh.write(','.join(names[i] for i in use)+'\n%d\n'%P)
        fh.write(',\n'.join(tostr(f,names) for f in polys)+'\n')
    return len(polys)
def msolve(path,timeout=110):
    out=path+'.out'
    if os.path.exists(out): os.remove(out)
    subprocess.run(['/home/claude/tools/gb/msolve','-g','2','-f',path,'-o',out],timeout=timeout,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
    txt=open(out).read(); body=txt[txt.index('['):]
    if body.strip().startswith('[1]:'): return 'unit',body
    n=body.count(',\n')+1; return n,body
