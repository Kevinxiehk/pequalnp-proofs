# VF-B generator (COMPUTE-verifyfl.md B): N-problem for defect line C m, written as a Singular script mod P
import sys, itertools, random
P=int(sys.argv[1]); mspec=sys.argv[2]; out=sys.argv[3]; seed=int(sys.argv[4]) if len(sys.argv)>4 else 1
p=P
def sqrtm(a):
    a%=p
    if a==0: return 0
    assert pow(a,(p-1)//2,p)==1
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
g=2
while True:   # primitive root -> fifth root of unity
    if all(pow(g,(p-1)//q,p)!=1 for q in set(f for f in [2,3,5]+[r for r in range(7,1000) if (p-1)%r==0 and all(r%d for d in range(2,int(r**.5)+1))] if (p-1)%f==0)): break
    g+=1
z5=pow(g,(p-1)//5,p); assert z5!=1 and pow(z5,5,p)==1
sym={'i':I,'w':w,'z':z5}
def val(tok):
    tok=tok.strip(); neg=tok.startswith('-'); tok=tok.lstrip('-')
    if tok.isdigit(): v=int(tok)
    elif tok in sym: v=sym[tok]
    elif tok[0] in sym and tok[1]=='^': v=pow(sym[tok[0]],int(tok[2:]),p)
    else: raise ValueError(tok)
    return (-v)%p if neg else v%p
m=[val(x) for x in mspec.split(',')]
assert len(m)==5 and sum(m)%p==0, 'sum m != 0'
Ps=[j for j in range(5) if m[j]]; q=len(Ps)
nf=3*(q-1)
NV=2+2*nf      # k,t, z-free, s-free
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
def build(off,colsum):
    M=[[{} for _ in range(5)] for _ in range(4)]
    idx=0
    for r in range(3):
        for j in Ps[:-1]: M[r][j]=var(off+idx); idx+=1
    for r in range(3):
        v={}
        for j in Ps[:-1]: v=add(v,M[r][j],-1)
        M[r][Ps[-1]]=v
    for j in Ps:
        v=const(colsum[j])
        for r in range(3): v=add(v,M[r][j],-1)
        M[3][j]=v
    return M
Z=build(2,m); Zs=build(2+nf,[0]*5)
# sanity: row sums 0
for M in (Z,Zs):
    for r in range(4):
        v={}
        for j in range(5): v=add(v,M[r][j])
        assert v=={}, 'row sum'
Y=[[add(mul(var(0),Z[r][c]),mul(var(1),Zs[r][c])) for c in range(5)] for r in range(4)]
def Cj(j):
    cols=[c for c in range(5) if c!=j]; tot={}
    for s in itertools.permutations(range(4)):
        pr=const(1)
        for r in range(4): pr=mul(pr,add(const(1),Y[r][cols[s[r]]]))
        tot=add(tot,pr)
    return add(tot,const(-24))
C=[Cj(j) for j in range(5)]
# basis of {w : w.m = 0}: e_j for j not in P, and (m_b e_a - m_a e_b) for a = P[0], b in P[1:]
W=[]
for j in range(5):
    if j not in Ps: W.append([1 if c==j else 0 for c in range(5)])
a=Ps[0]
for b in Ps[1:]:
    r=[0]*5; r[a]=m[b]; r[b]=(-m[a])%p; W.append(r)
assert len(W)==4
eqs={}
for ii,wr in enumerate(W):
    v={}
    for j in range(5):
        if wr[j]: v=add(v,mul(const(wr[j]),C[j]))
    for k,c in v.items():
        key=(ii,k[:2]); mk=(0,0)+k[2:]
        e=eqs.setdefault(key,{}); e[mk]=(e.get(mk,0)+c)%p
polys=[{k:v for k,v in e.items() if v} for e in eqs.values()]; polys=[x for x in polys if x]
# (3) normal form per column j in P
q34=3*inv(4)%p
for j in Ps:
    z0=[add(Z[r][j],const(-m[j]*inv(4))) for r in range(4)]
    zs=[Zs[r][j] for r in range(4)]
    dot=lambda u,v: (lambda acc: acc)(sum_poly([mul(u[r],v[r]) for r in range(4)]))
    def sum_poly(L):
        t={}
        for x in L: t=add(t,x)
        return t
    polys.append(add(sum_poly([mul(z0[r],z0[r]) for r in range(4)]),const(-q34*m[j]*m[j])))
    polys.append(sum_poly([mul(zs[r],zs[r]) for r in range(4)]))
    polys.append(sum_poly([mul(z0[r],zs[r]) for r in range(4)]))
# gauge: generic linear eq on Z entries (=0), generic affine eq on Zs entries (=1)
rnd=random.Random(seed)
lz={}; ls=const(-1)
for r in range(4):
    for j in Ps:
        lz=add(lz,mul(const(rnd.randrange(1,p)),Z[r][j])); ls=add(ls,mul(const(rnd.randrange(1,p)),Zs[r][j]))
polys+= [lz,ls]
names=['z%d'%i for i in range(nf)]+['s%d'%i for i in range(nf)]
def fmt(qq):
    terms=[]
    for k,v in qq.items():
        mon='*'.join(('%s^%d'%(names[i-2],k[i]) if k[i]>1 else names[i-2]) for i in range(2,NV) if k[i])
        terms.append(str(v)+('*'+mon if mon else ''))
    return '+'.join(terms) if terms else '0'
satcols=[[fmt(Zs[r][j]) for r in range(4)] for j in Ps]
with open(out,'w') as f:
    f.write('LIB "elim.lib";\noption(redSB);\nring R=%d,(%s),dp;\n'%(p,','.join(names)))
    f.write('ideal I=\n'+',\n'.join(fmt(x) for x in polys)+';\n')
    f.write('ideal G0=std(I); "before saturation: dim", dim(G0), "unit", (G0[1]==1);\n')
    f.write('ideal J=G0;\n')
    for k,col in enumerate(satcols):
        f.write('ideal K%d=%s;\nJ=sat(J,K%d);\n'%(k,','.join(col),k))
    f.write('ideal G=std(J);\n"after saturation: dim", dim(G), "unit", (G[1]==1);\nif (dim(G)==0) { "vdim (number of points with mult.)", vdim(G); }\nquit;\n')
print('m',mspec,'support',Ps,'unknowns',2*nf,'eqs',len(polys),file=sys.stderr)
