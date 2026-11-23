# verify2 round 6: OWN generator for VF-A (independent of local/results/VF-A/gen.py), msolve input.
#   usage: own_gen_A.py P CASE MODE OUTPREFIX     CASE in A1..A4, CAL;  MODE in charts | hom
# Differences from gen.py: E is a general 4x5 matrix (20 variables) with the 4 linear equations "column sums in C m";
# C_j(Y) - 24 = sum over nonempty column sets S not containing j of (4-|S|)! G_S(Y), G_S = coefficient of y_S in prod_r (1 + sum_c Y_rc y_c)
# in the squarefree algebra; N is removed by setting two entries of E to 0 where (Z, Zs) has an invertible 2x2 minor; charts E[r][c] = 1.
import sys, itertools, math
p=int(sys.argv[1]); case=sys.argv[2]; mode=sys.argv[3]; outp=sys.argv[4]
def sqrtm(a):
    a%=p
    for cand in (pow(a,(p+1)//4,p),) if p%4==3 else ():
        return cand
    # Cipolla
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
    assert r[1]==0 and r[0]*r[0]%p==a; return r[0]
inv=lambda a: pow(a%p,p-2,p)
I=sqrtm(p-1); s3=sqrtm(3); w=(-1+I*s3)*inv(2)%p; assert (w*w+w+1)%p==0
chi1=[1,I,p-1,(p-I)%p]; chi2=[1,p-1,1,p-1]; m=[1,w,w*w%p,0,0]; mbar=[1,w*w%p,w,0,0]
sb=1 if case in ('A1','A2','CAL') else -1; sx=1 if case in ('A1','A3','CAL') else -1
beta=sb*s3*inv(4)%p; xi=sx*sqrtm(-3*inv(32*beta))%p
h0=[(inv(4)+beta*c)%p for c in chi2]; lam=[0,xi,(p-xi)%p,0,0]
Z=[[(h0[r]*m[c]+chi1[r]*lam[c])%p for c in range(5)] for r in range(4)]; Zs=[[chi1[r]*mbar[c]%p for c in range(5)] for r in range(4)]
# variables: 0 = k, 1 = t, 2 = x, 3 + 5r + c = E[r][c];  monomial = sorted tuple of variable indices
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
Y=[[None]*5 for _ in range(4)]
for r in range(4):
    for c in range(5):
        f={(2,3+5*r+c):1}
        if case!='CAL' and Z[r][c]: f[(0,)]=Z[r][c]
        if Zs[r][c]: f[(1,)]=Zs[r][c]
        Y[r][c]=f
# G_S by dynamic programming over the rows
G={0:{():1}}
for r in range(4):
    G2={S:dict(q) for S,q in G.items()}
    for S,q in G.items():
        for c in range(5):
            if S>>c&1: continue
            T=S|1<<c; G2.setdefault(T,{}); padd(G2[T],pmul(q,Y[r][c]))
    G=G2
Wm=[[0,0,0,1,0],[0,0,0,0,1],[w,p-1,0,0,0],[w*w%p,0,p-1,0,0]]
R=[]
for wr in Wm:
    f={}
    for j in range(5):
        if not wr[j]: continue
        for S,q in G.items():
            if S==0 or S>>j&1: continue
            padd(f,q,wr[j]*math.factorial(4-bin(S).count('1'))%p)
    R.append(f)
eqs=[]; xfree=0
for f in R:
    by={}
    for mon,v in f.items():
        key=tuple(x for x in mon if x<3); rest=tuple(x for x in mon if x>=3)
        if 2 not in key: xfree+=1; continue
        by.setdefault(key,{}); by[key][rest]=(by[key].get(rest,0)+v)%p
    eqs+=[{k:v for k,v in q.items() if v} for q in by.values()]
eqs=[q for q in eqs if q]
# E in A_m: (column-sum vector) . w = 0 for the four w
for wr in Wm:
    q={}
    for c in range(5):
        if wr[c]:
            for r in range(4): q[(3+5*r+c,)]=wr[c]
    eqs.append(q)
# remove N: two entries with invertible minor
gens=[Z,Zs] if case!='CAL' else [Zs]; cells=[(r,c) for r in range(4) for c in range(5)]; zero=[]
if case!='CAL':
    for a,b in itertools.combinations(cells,2):
        if (Z[a[0]][a[1]]*Zs[b[0]][b[1]]-Z[b[0]][b[1]]*Zs[a[0]][a[1]])%p: zero=[a,b]; break
else:
    zero=[next(a for a in cells if Zs[a[0]][a[1]])]
for (r,c) in zero: eqs.append({(3+5*r+c,):1})
names={3+5*r+c:'E%d%d'%(r,c) for r in range(4) for c in range(5)}
def fmt(q): return '+'.join(str(v)+''.join('*'+names[x] for x in mon) for mon,v in q.items())
def write(fn,extra):
    with open(fn,'w') as f: f.write(','.join(names[3+i] for i in range(20))+'\n'+str(p)+'\n'+',\n'.join(fmt(q) for q in eqs+extra)+'\n')
print('case',case,'p',p,': x-free nonzero terms of R (must be 0 for A1..A4):',xfree,'; equations:',len(eqs),'; zeroed cells',zero,file=sys.stderr)
if mode=='hom': write(outp+'_hom.ms',[]); print(outp+'_hom.ms')
else:
    for (r,c) in cells:
        if (r,c) in zero: continue
        fn='%s_chart%d%d.ms'%(outp,r,c); write(fn,[{(3+5*r+c,):1,():p-1}]); print(fn)
