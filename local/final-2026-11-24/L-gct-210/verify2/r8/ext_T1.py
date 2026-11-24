# verify2 r9: exact T' (contains T_1) for stage2's candidates X (5x5, row 0 = r zero), and an integral complement basis U of X in T'.
import random, json, sys
from fractions import Fraction as F
random.seed(17)
def perm(M):
    n=len(M)
    if n==0: return F(1)
    return sum(M[0][j]*perm([r[:j]+r[j+1:] for r in M[1:]]) for j in range(n) if M[0][j]!=0)
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
def rank(rows,n): return n-len(null(rows,n))
def mk(cols0,rowparts):     # 5x5 flattened, row 0 zero; X rows 1..4
    B=[]
    for col in cols0:
        v=[F(0)]*25
        for i in range(4): v[(i+1)*5+0]=F(col[i])
        B.append(v)
    for row,w in rowparts:
        v=[F(0)]*25
        for l in range(5): v[(row+1)*5+l]=F(w[l])
        B.append(v)
    return B
cands={'D003P':mk([(0,0,1,-1),(1,-1,0,0)],[(2,(0,1,-1,0,0)),(3,(0,1,1,-1,-1)),(3,(0,0,0,1,-1))]),
       'D04P':mk([(F(3,10),F(-13,10),0,1)],[(2,(-4,1,1,1,1)),(2,(0,1,1,-1,-1)),(3,(0,1,-1,0,0)),(3,(0,0,0,1,-1))])}
out={}
for name,X in cands.items():
    rows=[]
    for _ in range(40):
        c=[random.randint(-6,6) for _ in range(5)]
        M=[[F(1)+sum(c[q]*X[q][i*5+j] for q in range(5)) for j in range(5)] for i in range(5)]
        rows.append([perm([[M[a][b] for b in range(5) if b!=j] for a in range(5) if a!=i]) for i in range(5) for j in range(5)])
    T=null(rows,25)
    # complement of X in T: greedy
    basis=[r[:] for r in X]; U=[]
    for t in T:
        if rank(basis+[t],25)>len(basis): basis.append(t); U.append(t)
    # integral scaling
    import math
    def integral(v):
        den=1
        for x in v: den=den*x.denominator//math.gcd(den,x.denominator)
        w=[int(x*den) for x in v]; g=0
        for x in w: g=math.gcd(g,abs(x))
        return [x//g for x in w] if g else w
    Ui=[integral(u) for u in U]; Xi=[integral(x) for x in X]
    print(name,'dim T\' =',len(T),' complement dim =',len(Ui),flush=True)
    out[name]={'X':Xi,'U':Ui}
json.dump(out,open('/home/kevxhk/work/L-gct-210/verify2/r8/ext_T1.json','w'))
