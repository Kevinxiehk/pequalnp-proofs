# verify2 r12: my own exact FO2 numbers over Q(sqrt -3) (pair arithmetic) for reg2's (2,1,1|1,1) IV-iso and (a,b) points and (a,a) leftovers.
# T' = null space of the first-order equations at 32 sample points (contains T_1: dim T' >= dim T_1); exact rank of q at 2 base points.
import itertools, random, sys
from fractions import Fraction as F
class Q3:
    __slots__=('a','b')
    def __init__(s,a=0,b=0): s.a=F(a); s.b=F(b)
    def __add__(s,o): o=o if isinstance(o,Q3) else Q3(o); return Q3(s.a+o.a,s.b+o.b)
    __radd__=__add__
    def __neg__(s): return Q3(-s.a,-s.b)
    def __sub__(s,o): return s+(-(o if isinstance(o,Q3) else Q3(o)))
    def __rsub__(s,o): return Q3(o)-s
    def __mul__(s,o): o=o if isinstance(o,Q3) else Q3(o); return Q3(s.a*o.a-3*s.b*o.b,s.a*o.b+s.b*o.a)
    __rmul__=__mul__
    def inv(s): n=s.a*s.a+3*s.b*s.b; return Q3(s.a/n,-s.b/n)
    def __truediv__(s,o): o=o if isinstance(o,Q3) else Q3(o); return s*o.inv()
    def iszero(s): return s.a==0 and s.b==0
    def __repr__(s): return '%s%+s*r3'%(s.a,s.b) if s.b else str(s.a)
Z0=Q3(0); ONE=Q3(1); R3=Q3(0,1); W=Q3(F(-1,2),F(1,2))      # w = (-1 + sqrt(-3))/2
def perm(M):
    n=len(M)
    if n==1: return M[0][0]
    tot=Z0
    for j in range(n):
        if not M[0][j].iszero(): tot=tot+M[0][j]*perm([r[:j]+r[j+1:] for r in M[1:]])
    return tot
def rank_null(rows,n):
    M=[r[:] for r in rows]; piv=[]; rk=0
    for c in range(n):
        p=next((i for i in range(rk,len(M)) if not M[i][c].iszero()),None)
        if p is None: continue
        M[rk],M[p]=M[p],M[rk]; iv=M[rk][c].inv(); M[rk]=[x*iv for x in M[rk]]
        for i in range(len(M)):
            if i!=rk and not M[i][c].iszero():
                f=M[i][c]; M[i]=[x-f*y for x,y in zip(M[i],M[rk])]
        piv.append(c); rk+=1
    free=[c for c in range(n) if c not in piv]; basis=[]
    for fc in free:
        v=[Z0]*n; v[fc]=ONE
        for i,pc in enumerate(piv): v[pc]=-M[i][fc]
        basis.append(v)
    return rk,basis
def q3(x): return x if isinstance(x,Q3) else Q3(x)
def rowel(i,w): m=[[Z0]*5 for _ in range(4)]; m[i]=[q3(x) for x in w]; return m
def colel(c,x):
    m=[[Z0]*5 for _ in range(4)]
    for i in range(4): m[i][c]=q3(x[i])
    return m
def full(B,c):
    M=[[ONE]*5 for _ in range(5)]
    for i in range(4):
        for l in range(5): M[i][l]=M[i][l]+sum((c[q]*B[q][i][l] for q in range(len(B))),Z0)
    return M
def cert(name,B):
    random.seed(5); d=len(B)
    lev=all((perm(full(B,[Q3(random.randint(-5,5)) for _ in range(d)]))-120).iszero() for _ in range(8))
    rows=[]
    for _ in range(32):
        M=full(B,[Q3(random.randint(-6,6)) for _ in range(d)])
        rows.append([perm([[M[a][b] for b in range(5) if b!=j] for a in range(5) if a!=i]) for i in range(5) for j in range(5)])
    rk,T=rank_null(rows,25); best=0
    for trial in range(2):
        M0=full(B,[Q3(random.randint(-4,4)) for _ in range(d)])
        G=[[Z0]*len(T) for _ in T]
        Q={}
        for (i,j),(k,l) in itertools.product(itertools.product(range(5),range(5)),repeat=2):
            if i!=k and j!=l: Q[(i*5+j,k*5+l)]=perm([[M0[a][b] for b in range(5) if b not in (j,l)] for a in range(5) if a not in (i,k)])
        for a in range(len(T)):
            for b in range(a,len(T)):
                s=sum((T[a][x]*v*T[b][y] for (x,y),v in Q.items() if not T[a][x].iszero() and not T[b][y].iszero()),Z0); G[a][b]=s; G[b][a]=s
        r,_=rank_null(G,len(T)); best=max(best,r)
    print('%-34s level %s dim T\' %d rank q %d => FO2 bound %d'%(name,lev,len(T),best,len(T)-(best+1)//2),flush=True)
c3=lambda u:[u[1]-u[2],u[2]-u[0],u[0]-u[1],Z0,Z0]
cr=lambda x:[Z0,x[2]-x[3],x[3]-x[1],x[1]-x[2]]
h=Q3(F(1,2)); W2=W*W
mode=sys.argv[1]
if mode=='iso':
    l=[ONE,W,W2,Z0,Z0]; U0i=[rowel(0,[1,1,1,-3,0]),rowel(0,[0,0,0,1,-1])]
    for p in [Q3(0),Q3(-2),-h,Q3(1),W,W2,None]:
        x=[Z0,Z0,ONE,-ONE] if p is None else [Z0,ONE,p,-ONE-p]
        cert('IV-iso p=%s'%('inf' if p is None else p),U0i+[rowel(1,l),rowel(2,l),colel(3,x),colel(4,cr(x))])
if mode=='ab':
    g=[ONE,ONE,ONE,Z0,Q3(-3)]
    for (s_,q) in [(-1,0),(-h,0),(1,0),(-2,0),(-1,4),(-1,-2),(0,W),(-1,-h),(0,2),(-1,1),(0,-1),(0,h)]:
        s_=q3(s_); q=q3(q); u1=[ONE,s_,-ONE-s_,Z0,Z0]; cu=c3(u1); u2=[g[j]+q*cu[j] for j in range(5)]
        _,Wn=rank_null([[ONE]*5,u1,u2],5)
        cert('ab s=%s q=%s'%(s_,q),[rowel(0,v) for v in Wn]+[rowel(1,u1),rowel(2,u2),colel(3,[0,1,-2,1]),colel(4,[0,1,0,-1])])
if mode=='aa':
    U0=[rowel(0,[-1,-1,-1,4,-1]),rowel(0,[-1,-1,-1,-1,4])]
    for (s,p) in [(1,-h),(-2,-h),(-h,-h),(0,-2),(-1,-2),(-2,1),(W,1),(0,0),(-1,0)]:
        s=q3(s); p=q3(p); u1=[ONE,s,-ONE-s,Z0,Z0]; x=[Z0,ONE,p,-ONE-p]
        cert('aa s=%s p=%s'%(s,p),U0+[rowel(1,u1),rowel(2,c3(u1)),colel(3,x),colel(4,cr(x))])
