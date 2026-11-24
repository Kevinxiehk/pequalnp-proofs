# R7 generator for R6-1 cases B (4 active columns) and C (5 active columns), "generic-h" charts (rows, round 7).
#   usage: python3 x4c2.py P CASE CHART OUT        CASE in {B, C, B3}; CHART = one digit 0..2 per active column (nondecreasing)
# Unknowns: Walsh coordinates x[j][q] of h and y[j][q] of h' (active columns j), normalised by
#   sigma(h)_0 = 1, sigma(h')_0 = 0, sigma(h')_1 = 1        (S_3 on Walsh indices fixes the ordered pair (p,q) = (0,1))
# and Rabinowitsch z_j * x[j][k_j] = 1 (coordinate k_j of column j of h nonzero; h is a GENERIC element of the plane:
# the freedom (h,h') -> (h + t h', h') is kept, so solutions come in curves; emptiness <=> unit ideal).
# Cover: every strongly level plane with injective row sums and all active columns nonzero has a point in one of the
# charts (multisets of k_j up to the column symmetry): B: 15 charts, C: 21 charts.  Equations: all (s,t)-coefficients of
# C_j(s h + t h') - 24 (degrees 2..4), j = 0..4.  Output: msolve file OUT.ms and Singular file OUT.sing (std, dim, unit).
import sys
p=int(sys.argv[1]); case=sys.argv[2]; chart=sys.argv[3]; out=sys.argv[4]
NSLICE=int(sys.argv[5]) if len(sys.argv)>5 else 0
FIX=int(sys.argv[6]) if len(sys.argv)>6 else None   # if given: sigma(h)_1 = FIX (kills the fibre h -> h + t h'; use nact+1 distinct values for a cover)   # random affine slices (only to make NON-unit cases 0-dimensional; never used for a unit verdict)
H=[[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]]
nact={'B':4,'C':5,'B3':3}[case]; assert len(chart)==nact
names=[]
def newvar(n): names.append(n); return len(names)-1
X=[[newvar('x%d%d'%(a,q)) for q in range(3)] for a in range(nact)]
Yv=[[newvar('y%d%d'%(a,q)) for q in range(3)] for a in range(nact)]
Z=[newvar('z%d'%a) for a in range(nact)]
S=newvar('s'); T=newvar('t'); NV=len(names)
def mono(i): e=[0]*NV; e[i]=1; return tuple(e)
ZERO=tuple([0]*NV); one={ZERO:1}
def add(a,b,c=1):
    r=dict(a)
    for k,v in b.items():
        w=(r.get(k,0)+c*v)%p
        if w: r[k]=w
        elif k in r: del r[k]
    return r
def mul(a,b):
    r={}
    for k1,v1 in a.items():
        for k2,v2 in b.items():
            k=tuple(x+y for x,y in zip(k1,k2)); r[k]=(r.get(k,0)+v1*v2)%p
    return {k:v for k,v in r.items() if v}
def var(i): return {mono(i):1}
# columns as polynomials; last active column's coordinates eliminated by the normalisation where needed
def cols(V,targets):   # targets: dict q -> required value of sigma_q (or None)
    C=[[var(V[a][q]) for q in range(3)] for a in range(nact)]
    for q,val in targets.items():
        e={ZERO:val%p} if val else {}
        for a in range(nact-1): e=add(e,C[a][q],-1)
        C[nact-1][q]=e
    return C
Ch=cols(X,{0:1} if FIX is None else {0:1,1:FIX}); Cp=cols(Yv,{0:0,1:1})
used=set()
for C_ in (Ch,Cp):
    for col in C_:
        for e in col:
            for k in e: 
                for i,x in enumerate(k):
                    if x: used.add(i)
Y=[[None]*5 for _ in range(4)]
sv=var(S); tv=var(T)
for i in range(4):
    for a in range(5):
        if a>=nact: Y[i][a]={}; continue
        e={}; f={}
        for q in range(3): e=add(e,Ch[a][q],H[i][q]); f=add(f,Cp[a][q],H[i][q])
        Y[i][a]=add(mul(sv,e),mul(tv,f))
def Cj(j):
    cl=[c for c in range(5) if c!=j]; M=[[add(one,Y[i][c]) for c in cl] for i in range(4)]; memo={}
    def pr(i,mask):
        if i==4: return one
        if (i,mask) in memo: return memo[(i,mask)]
        r={}
        for c in range(4):
            if not (mask>>c)&1: r=add(r,mul(M[i][c],pr(i+1,mask|(1<<c))))
        memo[(i,mask)]=r; return r
    return add(pr(0,0),{ZERO:(-24)%p})
eqs=[]
for j in range(5):
    parts={}
    for k,v in Cj(j).items():
        key=(k[S],k[T]); kk=list(k); kk[S]=0; kk[T]=0; parts.setdefault(key,{})[tuple(kk)]=v
    for key,pol in sorted(parts.items()):
        assert sum(key)>0
        if pol and pol not in eqs: eqs.append(pol)
for a in range(nact):
    eqs.append(add(mul(var(Z[a]),Ch[a][int(chart[a])]),{ZERO:p-1}))
import random
rnd=random.Random(1000+NSLICE)
for sl in range(NSLICE):
    e={ZERO:rnd.randrange(1,p)}
    for i in sorted(used):
        if names[i] not in ('s','t'): e=add(e,var(i),rnd.randrange(1,p))
    eqs.append(e)
uv=[i for i in range(NV) if i in used or i in Z]; uv=[i for i in uv if names[i] not in ('s','t')]
def show(pol):
    terms=[]
    for k,v in sorted(pol.items()):
        m='*'.join(('%s^%d'%(names[i],e) if e>1 else names[i]) for i,e in enumerate(k) if e)
        terms.append('%d%s'%(v,'*'+m if m else ''))
    return '+'.join(terms) if terms else '0'
vs=','.join(names[i] for i in uv)
with open(out+'.ms','w') as f: f.write(vs+'\n%d\n'%p+',\n'.join(show(e) for e in eqs)+'\n')
with open(out+'.sing','w') as f:
    f.write('ring r=%d,(%s),dp; option(redSB);\nideal I=\n%s;\nideal G=std(I);\nprintf("X4C2 %s chart %s p=%d: dim %%s unit %%s size %%s",dim(G),(reduce(1,G)==0),size(G));\nquit;\n'%(p,vs,',\n'.join(show(e) for e in eqs),case,chart,p))
print('written',out,len(eqs),'equations',len(uv),'unknowns')
