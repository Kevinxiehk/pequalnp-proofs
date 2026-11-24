# verify2 r7: independent re-derivation of the defect equations of gen_n2 ([T31]) and gen_n3 ([T22]), m = (1,2,-3,0,0).
# Hook exactlib.equations to capture the generator matrices B and gen's defect polynomials; recompute the defect equations with MY
# permanent / arithmetic / basis of m^perp; compare F_p-spans of (mine + gen's non-defect extras) with gen's full list.
# usage: python3 -I sl_indep_eqs.py n2 a|b    |   python3 -I sl_indep_eqs.py n3 FROM TO
import sys, itertools, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/verifyfl/exact')
import exactlib as X, gen_n1s, gen_n2, gen_n3
p=2147483629
CAP={}
orig=X.equations
def cap(B,W,pp,keyed=False):
    r=orig(B,W,pp,keyed) if keyed else orig(B,W,pp)
    CAP['B']=B; CAP['eqs']=r[0] if not keyed else None
    return r
X.equations=cap
def conv(q,nv):          # exactlib poly {sorted tuple of ids: c} -> {exponent tuple (len nv): c}
    out={}
    for mon,c in q.items():
        e=[0]*nv
        for i in mon: e[i]+=1
        out[tuple(e)]=(out.get(tuple(e),0)+c)%p
    return {k:v for k,v in out.items() if v}
def add(a,b,cb=1):
    r=dict(a)
    for k,v in b.items():
        x=(r.get(k,0)+cb*v)%p
        if x: r[k]=x
        elif k in r: del r[k]
    return r
def mul(a,b):
    r={}
    for k1,v1 in a.items():
        for k2,v2 in b.items():
            k=tuple(x+y for x,y in zip(k1,k2)); r[k]=(r.get(k,0)+v1*v2)%p
    return {k:v for k,v in r.items() if v}
def perm4(A):
    tot={}
    for s in itertools.permutations(range(4)):
        t=A[0][s[0]]
        for i in range(1,4): t=mul(t,A[i][s[i]])
        tot=add(tot,t)
    return tot

def mine_from_B(B,nu):
    k=len(B); nv=nu+k; one=tuple([0]*nv)
    Bc=[[[conv(B[r][a][c],nv) for c in range(5)] for a in range(4)] for r in range(k)]
    Y=[[{} for c in range(5)] for a in range(4)]
    for r in range(k):
        xr=[0]*nv; xr[nu+r]=1; xr={tuple(xr):1}
        for a in range(4):
            for c in range(5): Y[a][c]=add(Y[a][c],mul(xr,Bc[r][a][c]))
    C=[]
    for j in range(5):
        A=[[add({one:1},Y[a][c]) for c in range(5) if c!=j] for a in range(4)]
        C.append(add(perm4(A),{one:24},-1))
    Wm=[[2,-1,0,0,0],[3,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1]]
    eqs=[]
    for w in Wm:
        R={}
        for j in range(5):
            if w[j]: R=add(R,C[j],w[j])
        byx={}
        for e,c in R.items(): byx.setdefault(e[nu:],{})[e[:nu]]=c
        eqs+=list(byx.values())
    return eqs
def rank(rows,cols):
    if not rows: return 0
    M=np.array([[r.get(c,0) for c in cols] for r in rows],dtype=np.int64)%p; rk=0; n,m=M.shape
    for j in range(m):
        piv=None
        for i in range(rk,n):
            if M[i,j]: piv=i; break
        if piv is None: continue
        M[[rk,piv]]=M[[piv,rk]]; M[rk]=(M[rk]*pow(int(M[rk,j]),p-2,p))%p
        for i in range(n):
            if i!=rk and M[i,j]:
                f=int(M[i,j]); M[i]=(M[i]-f*M[rk])%p
        rk+=1
    return rk

def compare(tag,names,polys):
    nu=len(names); B=CAP['B']; geq=CAP['eqs']
    key=lambda q: tuple(sorted(q.items()))
    gset={}
    for q in geq:
        if q: gset[key(q)]=gset.get(key(q),0)+1
    extras=[]
    for q in polys:
        if not q: continue
        kq=key(q)
        if gset.get(kq,0): gset[kq]-=1
        else: extras.append(q)
    me=[conv(q,nu) for q in mine_from_B(B,nu)] if False else mine_from_B(B,nu)
    ex=[conv(q,nu) for q in extras]; th=[conv(q,nu) for q in polys if q]
    allm=[q for q in me+ex if q]
    cols=sorted(set().union(*[set(q) for q in allm+th]))
    r1=rank(allm,cols); r2=rank(th,cols); r12=rank(allm+th,cols)
    print('%s: extras %d, rank mine+extras %d, theirs %d, union %d -> %s'%(tag,len(extras),r1,r2,r12,'SAME SPAN' if r1==r2==r12 else 'DIFFERENT'),flush=True)
mode=sys.argv[1]
if mode=='n2':
    st=sys.argv[2]
    for cell in gen_n2.cells(p,'m12m3'):
        names,polys=gen_n2.build(p,'m12m3',cell,stage=st); compare('T31 stage %s cell %d'%(st,cell),names,polys)
else:
    cl=gen_n1s.cases(2); a,b=int(sys.argv[2]),int(sys.argv[3])
    for i in range(a,min(b,len(cl))):
        for s in (0,1,2):
            names,polys=gen_n3.build(p,'m12m3',cl[i],s); compare('T22 case %d %s scell %d'%(i,cl[i],s),names,polys)
