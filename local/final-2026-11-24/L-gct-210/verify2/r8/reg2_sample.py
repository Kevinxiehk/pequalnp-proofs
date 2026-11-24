# verify2 r9: independent EXACT sample check of reg2's families (secs 8.2, 8.3, 9.4-D, 11.1-11.5): for rational members M (6-dim 4x5,
# embedded as rows 0..3 of 5x5, row 4 = r zero): exact level identity (polynomial in the coordinates), exact T' (annihilator of cofactors
# at 30 integer points; T' contains T_1, so dim T' is an exact UPPER bound for dim T_1), dim Omega' = rank of the row-4 part of T'.
import itertools, random
from fractions import Fraction as F
random.seed(9)
def vec(*a): return [F(x) for x in a]
def outer_col(x,c):      # x in C^4 (rows 0..3) placed in column c
    M=[[F(0)]*5 for _ in range(4)]
    for i in range(4): M[i][c]=F(x[i])
    return M
def outer_row(i,w):
    M=[[F(0)]*5 for _ in range(4)]; M[i]=[F(x) for x in w]; return M
def null(rows,n):
    M=[[F(x) for x in r] for r in rows]; piv=[]; rk=0
    for c in range(n):
        p=next((i for i in range(rk,len(M)) if M[i][c]!=0),None)
        if p is None: continue
        M[rk],M[p]=M[p],M[rk]; pv=M[rk][c]; M[rk]=[x/pv for x in M[rk]]
        for i in range(len(M)):
            if i!=rk and M[i][c]!=0:
                f=M[i][c]; M[i]=[x-f*y for x,y in zip(M[i],M[rk])]
        piv.append(c); rk+=1
    out=[]
    for fc in [c for c in range(n) if c not in piv]:
        v=[F(0)]*n; v[fc]=F(1)
        for r,pc in enumerate(piv): v[pc]=-M[r][fc]
        out.append(v)
    return out
def perm(M):
    n=len(M)
    if n==0: return F(1)
    return sum(M[0][j]*perm([r[:j]+r[j+1:] for r in M[1:]]) for j in range(n) if M[0][j]!=0)
def span_basis(B):        # independent subset
    rows=[[x for r in b for x in r] for b in B]; keep=[]; cur=[]
    for b,r in zip(B,rows):
        if len(null(cur+[r],20))<20-len(cur)-1+1 and (len(cur)==0 or len(null([*cur,r],20))==20-len(cur)-1): cur.append(r); keep.append(b)
    return keep
def analyse(name,B):
    d=len(B)
    def full(c):
        M=[[F(1)]*5 for _ in range(5)]
        for i in range(4):
            for l in range(5): M[i][l]+=sum(c[q]*B[q][i][l] for q in range(d))
        return M
    lev=all(perm(full([F(random.randint(-6,6)) for _ in range(d)]))==120 for _ in range(12))
    rows=[]
    for _ in range(30):
        M=full([F(random.randint(-6,6)) for _ in range(d)])
        rows.append([perm([[M[a][b] for b in range(5) if b!=j] for a in range(5) if a!=i]) for i in range(5) for j in range(5)])
    T=null(rows,25); om=25-len(null([t[20:25] for t in T],5)) if T else 0
    om=len(T)-len(null([[t[20+k] for t in T] for k in range(5)],len(T))) if T else 0
    print('%-34s dim M %d  level(12 random pts, exact) %s  dim T\' %d  dim Omega\' %d'%(name,d,lev,len(T),om),flush=True)
def H(c,u):   # basis of {w in C^5: w_c = 0, sum w = 0, <w,u> = 0} (u may be None)
    rows=[[F(1)]*5,[F(1) if k==c else F(0) for k in range(5)]]+([[F(x) for x in u]] if u else [])
    return null(rows,5)
# 11.2 (2,1|3), c = 4, u in H_4 (u_0 = 1)
for (u1,u2) in [(2,3),(-1,5),(3,-7)]:
    u=[1,u1,u2,-1-u1-u2,0]
    B=[outer_row(0,w) for w in H(4,u)]+[outer_row(1,u)]+[outer_col(x,4) for x in ([1,-1,0,0],[0,1,-1,0],[0,0,1,-1])]
    analyse('11.2 (2,1|3) u=%s'%u,B)
# 11.1(a) (3|2,1): row 0 = H_4, x' = (0,1,p,-1-p) in column 3, V = x'^perp cap 1^perp in column 4
for p in (2,-3,5):
    xp=[0,1,p,-1-p]; V=null([[1,1,1,1],xp],4)
    B=[outer_row(0,w) for w in H(4,None)]+[outer_col(v,4) for v in V]+[outer_col(xp,3)]
    analyse('11.1a (3|2,1) p=%s'%p,B)
# 11.3 (b-i): row 0 = H_4; column 4: x1 = (3,-1,-1,-1); columns 3, 2: x2 = (0,1,p,-1-p), x3 perp x2 in {x_0=0,sum=0}
for p in (2,-3):
    x2=[0,1,p,-1-p]; x3=null([[1,0,0,0],[1,1,1,1],x2],4)[0]
    B=[outer_row(0,w) for w in H(4,None)]+[outer_col([3,-1,-1,-1],4),outer_col(x2,3),outer_col(x3,2)]
    analyse('11.3b-i (3|1,1,1) p=%s'%p,B)
# 11.4 V0: column 4: V = {x_0 = 0, sum 0}; column 3: x' = (3,-1,-1,-1); row 1: u in H_34; row 0: U_0 = {w_3 = 0, sum 0, <w,u> = 0}
for s in (2,-5):
    u=[1,s,-1-s,0,0]; U0=null([[1]*5,[0,0,0,1,0],u],5)
    B=[outer_row(0,w) for w in U0]+[outer_row(1,u)]+[outer_col(v,4) for v in ([0,1,-1,0],[0,0,1,-1])]+[outer_col([3,-1,-1,-1],3)]
    analyse('11.4 V0 (2,1|2,1) s=%s'%s,B)
# 11.5 A1: rows 0,1,2: u0 = (1,1,1,0,-3), u1 = (1,s,-1-s,0,0), u2 perp u1 in H_34; column 4: V = {x_0=0,sum 0}; column 3: (3,-1,-1,-1)
for s in (2,-5):
    u1=[1,s,-1-s,0,0]; u2=null([[1]*5,[0,0,0,1,0],[0,0,0,0,1],u1],5)[0]
    B=[outer_row(0,[1,1,1,0,-3]),outer_row(1,u1),outer_row(2,u2)]+[outer_col(v,4) for v in ([0,1,-1,0],[0,0,1,-1])]+[outer_col([3,-1,-1,-1],3)]
    analyse('11.5 A1 (1,1,1|2,1) s=%s'%s,B)
# 9.4 locus D: b = e1-e2, c = e3-e4 (columns 1..4), a = (1,1,-1,-1); U_0 = span(5e_0 - 1, (0,a)); V = {x_0 = 0, sum 0} in column 0
B=[outer_row(0,[4,-1,-1,-1,-1]),outer_row(0,[0,1,1,-1,-1]),outer_row(1,[0,1,-1,0,0]),outer_row(2,[0,0,0,1,-1])]+[outer_col(v,0) for v in ([0,1,-1,0],[0,0,1,-1])]
analyse('9.4 DR211-ii locus D (claim T_1 = 10)',B)
# 8.2 NC member: {x e_0^T : sum x = 0} + e_0 w0 + e_1 w1 + e_3 w3, w0 = (1,-1,0,0), w1 = (0,0,1,-1), w3 = (1,1,-1,-1) on columns 1..4
B=[outer_col(v,0) for v in ([1,-1,0,0],[0,1,-1,0],[0,0,1,-1])]+[outer_row(0,[0,1,-1,0,0]),outer_row(1,[0,0,0,1,-1]),outer_row(3,[0,1,1,-1,-1])]
analyse('8.2 NC member (claim T_1 = 9)',B)
# 8.3 DR22: mu = (0,1,m3,m4) on columns 1..4; U_0 = {w_0 = 0, sum 0, <mu,w'> = 0}; U_1 = span(5e_0 - 1, (0, mu - mean)); V = {x_1 = 0, sum 0} col 0
for (m3,m4,lab) in [(2,5,'generic (claim 9)'),(3,-2,'generic (claim 9)'),(0,1,'0/1 vector (claim 10)'),(1,1,'0/1 vector (claim 10)')]:
    mu=[0,1,m3,m4]; mean=F(sum(mu),4); U0=null([[1]*5,[1,0,0,0,0],[0]+mu],5)
    B=[outer_row(0,w) for w in U0]+[outer_row(1,[4,-1,-1,-1,-1]),outer_row(1,[0]+[F(x)-mean for x in mu])]+[outer_col(v,0) for v in ([1,0,-1,0],[0,0,1,-1])]
    analyse('8.3 DR22 mu=%s %s'%(mu,lab),B)
