# Calibration check for VF-B |P|=3, m=(1,w,w^2,0,0): are the 24 points exactly the row-permuted A planes (gauge-normalised)?
import sys, itertools, random
P=int(sys.argv[1]); seed=int(sys.argv[2]); out=sys.argv[3]; p=P
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
m=[1,w,w*w%p,0,0]; mbar=[1,w*w%p,w,0,0]; Ps=[0,1,2]
chi1=[1,I,p-1,(-I)%p]; chi2=[1,p-1,1,p-1]
pts=set()
rnd=random.Random(seed)
# replicate the generator's gauge coefficients: same RNG call order (lz, ls interleaved over r, j)
lzc={}; lsc={}
for r in range(4):
    for j in Ps: lzc[(r,j)]=rnd.randrange(1,p); lsc[(r,j)]=rnd.randrange(1,p)
for sb in (1,-1):
    beta=sb*s3*inv(4)%p
    a=(-3*inv(32*beta))%p
    if pow(a,(p-1)//2,p)!=1: print('xi not in F_p for this prime'); sys.exit(1)
    for sx in (1,-1):
        xi=sx*sqrtm(a)%p
        h0=[(inv(4)+beta*c)%p for c in chi2]; lam=[0,xi,(-xi)%p]
        Z=[[(h0[r]*m[j]+chi1[r]*(lam[j] if j<3 else 0))%p for j in range(5)] for r in range(4)]
        Zs=[[chi1[r]*mbar[j]%p for j in range(5)] for r in range(4)]
        for perm in itertools.permutations(range(4)):
            Zp=[Z[perm[r]] for r in range(4)]; Zsp=[Zs[perm[r]] for r in range(4)]
            ls=sum(lsc[(r,j)]*Zsp[r][j] for r in range(4) for j in Ps)%p
            Zs2=[[x*inv(ls)%p for x in row] for row in Zsp]
            lzZ=sum(lzc[(r,j)]*Zp[r][j] for r in range(4) for j in Ps)%p; lzS=sum(lzc[(r,j)]*Zs2[r][j] for r in range(4) for j in Ps)%p
            c=lzZ*inv(lzS)%p
            Z2=[[(Zp[r][j]-c*Zs2[r][j])%p for j in range(5)] for r in range(4)]
            free=tuple(Z2[r][j] for r in range(3) for j in Ps[:-1])+tuple(Zs2[r][j] for r in range(3) for j in Ps[:-1])
            pts.add(free)
print('distinct gauge-normalised row-permuted A planes:',len(pts),file=sys.stderr)
names=['z%d'%i for i in range(6)]+['s%d'%i for i in range(6)]
with open(out,'w') as f:
    f.write('int cnt=0; ideal Pt;\n')
    for pt in pts:
        f.write('Pt=std(ideal(%s)); if (size(reduce(G,Pt))==0) {cnt++;}\n'%','.join('%s-%d'%(n,v) for n,v in zip(names,pt)))
    f.write('"A-plane points on the variety:", cnt, "of", %d;\n'%len(pts))
