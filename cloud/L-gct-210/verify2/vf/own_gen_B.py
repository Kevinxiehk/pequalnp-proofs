# verify2 round 6: OWN generator for VF-B (N-problem), Singular script.  usage: own_gen_B.py P "m-spec" OUT [j0]
# Independent of local/results/VF-B/gen.py: Z, Zs are full 4 x |P| blocks of variables with the linear conditions (1) as equations;
# C_j - 24 via the squarefree-algebra expansion; gauge by the CHART  Zs[0][j0] = 1, Z[0][j0] = 0  (exact, given row-permutation symmetry:
# zs_{j0} != 0 has a nonzero entry, a row permutation moves it to row 0, Zs -> c' Zs makes it 1, Z -> Z + c Zs makes Z[0][j0] = 0);
# then successive saturation by the ideals (entries of zs_j), j in P, j != j0.
import sys, itertools, math
p=int(sys.argv[1]); mspec=sys.argv[2]; out=sys.argv[3]
def sqrtm(a):
    a%=p
    if a==0: return 0
    assert pow(a,(p-1)//2,p)==1
    t=1
    while pow((t*t-a)%p,(p-1)//2,p)!=p-1: t+=1
    w2=(t*t-a)%p
    def mul(u,v): return ((u[0]*v[0]+u[1]*v[1]*w2)%p,(u[0]*v[1]+u[1]*v[0])%p)
    r=(1,0); b=(t,1); e=(p+1)//2
    while e:
        if e&1: r=mul(r,b)
        b=mul(b,b); e>>=1
    assert r[1]==0; return r[0]
inv=lambda a: pow(a%p,p-2,p)
I=sqrtm(p-1); s3=sqrtm(3); w=(-1+I*s3)*inv(2)%p
def val(tok):
    tok=tok.strip(); neg=tok.startswith('-'); tok=tok.lstrip('-')
    if tok.isdigit(): v=int(tok)
    elif tok=='i': v=I
    elif tok=='w': v=w
    elif tok.startswith('w^'): v=pow(w,int(tok[2:]),p)
    elif tok.startswith('i^'): v=pow(I,int(tok[2:]),p)
    else: raise ValueError(tok)
    return (-v)%p if neg else v%p
m=[val(x) for x in mspec.split(',')]; assert sum(m)%p==0
Ps=[j for j in range(5) if m[j]]; q=len(Ps); j0=int(sys.argv[4]) if len(sys.argv)>4 else Ps[0]
# variables: 0 = k, 1 = t, then Z[r][j] and S[r][j] for j in Ps
vid={}; names={}
for r in range(4):
    for j in Ps:
        vid[('Z',r,j)]=len(vid)+2; names[vid[('Z',r,j)]]='Z%d%d'%(r,j)
for r in range(4):
    for j in Ps:
        vid[('S',r,j)]=len(vid)+2; names[vid[('S',r,j)]]='S%d%d'%(r,j)
def padd(a,b,c=1):
    for k,v in b.items():
        nv=(a.get(k,0)+c*v)%p
        if nv: a[k]=nv
        elif k in a: del a[k]
    return a
def pmul(a,b):
    r={}
    for k1,v1 in a.items():
        for k2,v2 in b.items():
            k=tuple(sorted(k1+k2)); nv=(r.get(k,0)+v1*v2)%p
            if nv: r[k]=nv
            elif k in r: del r[k]
    return r
Y=[[({(0,vid[('Z',r,c)]):1,(1,vid[('S',r,c)]):1} if c in Ps else {}) for c in range(5)] for r in range(4)]
G={0:{():1}}
for r in range(4):
    G2={S:dict(qq) for S,qq in G.items()}
    for S,qq in G.items():
        for c in Ps:
            if S>>c&1: continue
            T=S|1<<c; G2.setdefault(T,{}); padd(G2[T],pmul(qq,Y[r][c]))
    G=G2
W=[[1 if c==j else 0 for c in range(5)] for j in range(5) if j not in Ps]
for b in Ps[1:]:
    row=[0]*5; row[Ps[0]]=m[b]; row[b]=(p-m[Ps[0]])%p; W.append(row)
eqs=[]
for wr in W:
    f={}
    for j in range(5):
        if not wr[j]: continue
        for S,qq in G.items():
            if S==0 or S>>j&1: continue
            padd(f,qq,wr[j]*math.factorial(4-bin(S).count('1'))%p)
    by={}
    for mon,v in f.items():
        key=tuple(x for x in mon if x<2); rest=tuple(x for x in mon if x>=2); by.setdefault(key,{}); by[key][rest]=(by[key].get(rest,0)+v)%p
    eqs+=[{k:v for k,v in qq.items() if v} for qq in by.values()]
eqs=[e for e in eqs if e]
# (1) linear conditions
for r in range(4):
    eqs.append({(vid[('Z',r,j)],):1 for j in Ps}); eqs.append({(vid[('S',r,j)],):1 for j in Ps})
for j in Ps:
    e={(vid[('Z',r,j)],):1 for r in range(4)}; e[()]=(p-m[j])%p; eqs.append(e); eqs.append({(vid[('S',r,j)],):1 for r in range(4)})
# (3) normal form
q4=inv(4)
for j in Ps:
    z0=[{(vid[('Z',r,j)],):1,():(p-m[j]*q4)%p} for r in range(4)]; zs=[{(vid[('S',r,j)],):1} for r in range(4)]
    e={}
    for r in range(4): padd(e,pmul(z0[r],z0[r]))
    padd(e,{():(p-3*q4*m[j]*m[j])%p}); eqs.append(e)
    e={}
    for r in range(4): padd(e,pmul(zs[r],zs[r]))
    eqs.append(e); e={}
    for r in range(4): padd(e,pmul(z0[r],zs[r]))
    eqs.append(e)
# chart gauge
eqs.append({(vid[('S',0,j0)],):1,():p-1}); eqs.append({(vid[('Z',0,j0)],):1})
allv=sorted(names)
def fmt(e): return '+'.join(str(v)+''.join('*'+names[x] for x in mon) for mon,v in e.items()) if e else '0'
with open(out,'w') as f:
    f.write('LIB "elim.lib";\noption(redSB);\nring R=%d,(%s),dp;\n'%(p,','.join(names[x] for x in allv)))
    f.write('ideal I=\n'+',\n'.join(fmt(e) for e in eqs)+';\nideal J=std(I);\n"chart j0 = %d: before saturation: dim", dim(J), "unit", (J[1]==1);\n'%j0)
    for j in Ps:
        if j==j0: continue
        f.write('J=sat(J,ideal(%s));\n'%','.join(names[vid[('S',r,j)]] for r in range(4)))
    f.write('ideal Gs=std(J);\n"after saturation: dim", dim(Gs), "unit", (Gs[1]==1);\nif (dim(Gs)==0) { "vdim", vdim(Gs); }\nquit;\n')
print('m',mspec,'support',Ps,'variables',len(allv),'equations',len(eqs),file=sys.stderr)
