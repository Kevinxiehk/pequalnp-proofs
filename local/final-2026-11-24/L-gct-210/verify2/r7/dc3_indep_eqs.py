# verify2 r7: INDEPENDENT re-derivation of the [DC3] equations of verifyfl/exact/gen_n1s.py.
# Takes gen_n1s's cell parametrisation B (captured), recomputes  R_w(Y) = sum_j w_j (perm(J_4 + Y^(j)) - 24),  Y = sum_r x_r B_r,
# for MY basis w of m^perp, with my own polynomial arithmetic and my own permanent, extracts all x-coefficients, and compares the
# F_p-linear span with gen_n1s's polynomial list (equations + chart quadrics).  usage: python3 -I dc3_indep_eqs.py [case indices ...]
import sys, itertools, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/verifyfl/exact')
import exactlib as X, gen_n1s as G
p=2147483629
CAP={}
orig=X.equations
def cap(B,W,pp,keyed=False):
    CAP['B']=B; return orig(B,W,pp,keyed) if keyed else orig(B,W,pp)
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
def mine(case):
    names,polys=G.build(p,'m12m3',case); B=CAP['B']; k=len(B); nu=len(names); nv=nu+k
    one=tuple([0]*nv)
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
    Wm=[[2,-1,0,0,0],[3,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1]]     # my basis of m^perp, m = (1,2,-3,0,0)
    eqs=[]
    for w in Wm:
        R={}
        for j in range(5):
            if w[j]: R=add(R,C[j],w[j])
        byx={}
        for e,c in R.items():
            byx.setdefault(e[nu:],{})[e[:nu]]=c
        eqs+=list(byx.values())
    theirs=[conv(q,nu) for q in polys]
    return eqs,theirs,nu
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
cl=G.cases(3)
idx=[int(a) for a in sys.argv[1:]] or list(range(len(cl)))
for i in idx:
    case=cl[i]; eqs,theirs,nu=mine(case)
    extra=[q for q in theirs if q and not any(True for _ in [])]   # placeholder (all of theirs)
    # chart quadrics of 'ab' are not defect equations: add them to MY set (they are part of the parametrisation, audited by reading)
    quads=[]
    names,_=G.build(p,'m12m3',case)
    for nm in ('3','4'):
        if 'a'+nm in names:
            ia=names.index('a'+nm); ib=names.index('b'+nm)
            def var(t):
                e=[0]*nu; e[t]=1; return {tuple(e):1}
            a=var(ia); b=var(ib); one=tuple([0]*nu); last=add(add({one:p-1},a,-1),b,-1)
            q={one:1}
            for c_ in (a,b,last): q=add(q,mul(c_,c_))
            quads.append(q)
    mineall=[q for q in eqs+quads if q]; th=[q for q in theirs if q]
    cols=sorted(set().union(*[set(q) for q in mineall+th]))
    r1=rank(mineall,cols); r2=rank(th,cols); r12=rank(mineall+th,cols)
    print('case %3d %s: rank mine %d, theirs %d, union %d -> %s'%(i,case,r1,r2,r12,'SAME SPAN' if r1==r2==r12 else 'DIFFERENT'),flush=True)
