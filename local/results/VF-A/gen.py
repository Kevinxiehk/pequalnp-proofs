# VF-A generator: equations mod p for one-vector extensions of N (COMPUTE-verifyfl.md A), msolve format
import sys, itertools, random
p=int(sys.argv[1]); case=sys.argv[2]; out=sys.argv[3]; seed=int(sys.argv[4]) if len(sys.argv)>4 else 1
def sqrtm(a):
    a%=p
    if a==0: return 0
    assert pow(a,(p-1)//2,p)==1, 'non-residue'
    q,s=p-1,0
    while q%2==0: q//=2; s+=1
    z=2
    while pow(z,(p-1)//2,p)!=p-1: z+=1
    M,c,t,R=s,pow(z,q,p),pow(a,q,p),pow(a,(q+1)//2,p)
    while t!=1:
        i,tt=0,t
        while tt!=1: tt=tt*tt%p; i+=1
        b=pow(c,1<<(M-i-1),p); M,c,t,R=i,b*b%p,t*b*b%p,R*b%p
    return R
inv=lambda a: pow(a%p,p-2,p)
I=sqrtm(-1); s3=sqrtm(3); w=(-1+I*s3)*inv(2)%p
assert (w*w+w+1)%p==0
one=[1,1,1,1]; chi1=[1,I,p-1,(-I)%p]; chi2=[1,p-1,1,p-1]
m=[1,w,w*w%p,0,0]; mbar=[1,w*w%p,w,0,0]
NV=19   # vars: k,t,x, e0..e15
def var(i):
    e=[0]*NV; e[i]=1; return {tuple(e):1}
def add(a,b,cb=1):
    r=dict(a)
    for k,v in b.items():
        r[k]=(r.get(k,0)+cb*v)%p
        if r[k]==0: del r[k]
    return r
def mul(a,b):
    r={}
    for k1,v1 in a.items():
        for k2,v2 in b.items():
            k=tuple(x+y for x,y in zip(k1,k2)); r[k]=(r.get(k,0)+v1*v2)%p
    return {k:v for k,v in r.items() if v}
def const(c): return {tuple([0]*NV):c%p} if c%p else {}
def outer(u,v): return [[u[r]*v[c]%p for c in range(5)] for r in range(4)]
# N
if case in ('A1','A2','A3','A4','CAL'):
    sb=1 if case in ('A1','A2','CAL') else -1; sx=1 if case in ('A1','A3','CAL') else -1
    beta=sb*s3*inv(4)%p
    xi=sx*sqrtm(-3*inv(32*beta))%p
    h0=[(inv(4)+beta*c)%p for c in chi2]
    Z=[[ (outer(h0,m)[r][c]+outer(chi1,[0,xi,(-xi)%p,0,0])[r][c])%p for c in range(5)] for r in range(4)]
    Zs=outer(chi1,mbar)
gens=[Z,Zs] if case!='CAL' else [Zs]
# E in A_m: rows 0..2 free (e0..e14), lambda = e15, row 3 = lambda*m - sum rows
E=[[None]*5 for _ in range(4)]
for r in range(3):
    for c in range(5): E[r][c]=var(3+5*r+c)
for c in range(5):
    v=mul(const(m[c]),var(18))
    for r in range(3): v=add(v,E[r][c],-1)
    E[3][c]=v
# Y = k Z + t Zs + x E   (for CAL: t Zs + x E)
Y=[[None]*5 for _ in range(4)]
for r in range(4):
    for c in range(5):
        v=mul(var(2),E[r][c])
        if case!='CAL': v=add(v,const(Z[r][c]) and mul(const(Z[r][c]),var(0)) or {})
        v=add(v,const(Zs[r][c]) and mul(const(Zs[r][c]),var(1)) or {})
        Y[r][c]=v
def Cj(j):
    cols=[c for c in range(5) if c!=j]; tot={}
    for s in itertools.permutations(range(4)):
        pr=const(1)
        for r in range(4): pr=mul(pr,add(const(1),Y[r][cols[s[r]]]))
        tot=add(tot,pr)
    return add(tot,const(-24))
C=[Cj(j) for j in range(5)]
W=[[0,0,0,1,0],[0,0,0,0,1],[w,p-1,0,0,0],[w*w%p,0,p-1,0,0]]
for wr in W: assert sum(a*b for a,b in zip(wr,m))%p==0
R=[]
for wr in W:
    v={}
    for j in range(5):
        if wr[j]: v=add(v,mul(const(wr[j]),C[j]))
    R.append(v)
eqs={}; bad=0
for Ri in R:
    for k,v in Ri.items():
        key=k[:3]
        if key[2]==0:
            bad+=1; continue
        eqs.setdefault((id(Ri),key),{}); e=eqs[(id(Ri),key)]; mk=(0,0,0)+k[3:]; e[mk]=(e.get(mk,0)+v)%p
print('case',case,'p',p,'x-free nonzero terms (must be 0):',bad, file=sys.stderr)
polys=[ {k:v for k,v in e.items() if v} for e in eqs.values()]; polys=[q for q in polys if q]
rnd=random.Random(seed)
names=['e%d'%i for i in range(16)]
# normalisation: E modulo span(gens): for each generator g, one generic linear eq; plus one generic affine eq
lin=[]
for _ in range(len(gens)):
    lin.append({tuple([0,0,0]+[1 if j==i else 0 for j in range(16)]):rnd.randrange(1,p) for i in range(16)})
aff={tuple([0,0,0]+[1 if j==i else 0 for j in range(16)]):rnd.randrange(1,p) for i in range(16)}; aff[tuple([0]*NV)]=p-1
allp=polys+lin+[aff]
def fmt(q):
    terms=[]
    for k,v in q.items():
        mon='*'.join(('%s^%d'%(names[i-3],k[i]) if k[i]>1 else names[i-3]) for i in range(3,NV) if k[i])
        terms.append(str(v)+('*'+mon if mon else ''))
    return '+'.join(terms)
with open(out,'w') as f:
    f.write(','.join(names)+'\n'+str(p)+'\n'+',\n'.join(fmt(q) for q in allp)+'\n')
print('wrote',len(allp),'polys (',len(polys),'coefficient eqs)',file=sys.stderr)
