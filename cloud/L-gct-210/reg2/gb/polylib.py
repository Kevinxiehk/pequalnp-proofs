# tiny exact polynomial arithmetic over Z (dict: exponent tuple -> int) and msolve I/O
import itertools, subprocess, time
class Ring:
    def __init__(self,names): self.names=list(names); self.n=len(names); self.idx={v:i for i,v in enumerate(names)}
    def var(self,name):
        e=[0]*self.n; e[self.idx[name]]=1; return {tuple(e):1}
    def const(self,c): return {tuple([0]*self.n):c} if c else {}
def add(a,b,cb=1):
    r=dict(a)
    for k,v in b.items():
        s=r.get(k,0)+cb*v
        if s: r[k]=s
        elif k in r: del r[k]
    return r
def mul(a,b):
    r={}
    for k1,v1 in a.items():
        for k2,v2 in b.items():
            k=tuple(x+y for x,y in zip(k1,k2)); r[k]=r.get(k,0)+v1*v2
    return {k:v for k,v in r.items() if v}
def scal(a,c): return {k:v*c for k,v in a.items()} if c else {}
P4=list(itertools.permutations(range(4)))
def perm4(A):
    tot={}
    for p in P4:
        t=A[0][p[0]]
        for i in range(1,4): t=mul(t,A[i][p[i]])
        tot=add(tot,t)
    return tot
def coeffs_wrt(poly,R,ynames):
    """split poly by monomial in the y variables; returns dict ymono -> poly (with y exponents zeroed)"""
    yi=[R.idx[v] for v in ynames]; out={}
    for k,v in poly.items():
        ym=tuple(k[i] for i in yi); kk=list(k)
        for i in yi: kk[i]=0
        out.setdefault(ym,{})[tuple(kk)]=out.get(ym,{}).get(tuple(kk),0)+v
    return out
def to_str(poly,names,p):
    terms=[]
    for k,v in poly.items():
        c=v%p
        if c==0: continue
        mon='*'.join('%s^%d'%(names[i],e) if e>1 else names[i] for i,e in enumerate(k) if e)
        terms.append(('%d*%s'%(c,mon)) if mon else '%d'%c)
    return '+'.join(terms) if terms else '0'
def run_msolve(polys,names,p,tag,timeout=110):
    """polys: list of dict polys over the names (already restricted); returns (is_unit, nbasis, seconds)"""
    lines=[to_str(q,names,p) for q in polys]; lines=[l for l in lines if l!='0']
    fn='/tmp/gb_%s.ms'%tag; out='/tmp/gb_%s.out'%tag
    open(fn,'w').write(','.join(names)+'\n%d\n'%p+',\n'.join(lines)+'\n')
    t0=time.time()
    try:
        subprocess.run(['/home/claude/tools/gb/msolve','-g','2','-f',fn,'-o',out],timeout=timeout,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
    except subprocess.TimeoutExpired:
        return None,None,time.time()-t0
    txt=open(out).read()
    body=txt[txt.find('['):txt.rfind(']')+1] if '[' in txt else txt
    elems=[e.strip() for e in body.strip('[]').replace('\n','').split(',') if e.strip()]
    unit=(len(elems)==1 and elems[0] in ('1','[1]'))
    return unit,len(elems),time.time()-t0
