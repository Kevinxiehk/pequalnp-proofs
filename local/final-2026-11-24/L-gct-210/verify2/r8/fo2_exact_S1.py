# verify2 r8: EXACT FO2 bound for stage2's survivor (S1) (R9-4): X = L_r (rows 1..4 of 5x5, row 0 zero), integer basis.
# T' = {t : <C(J+m), t> = 0 for m at 40 integer points of X}  (T' contains T_1(X); FO2 stays valid on any T' containing L).
# q = Hessian of perm at J + m0 (one rational point m0); bound = dim T' - ceil(rank(q|T')/2)  (Lemma FO2, bilinear, no conjugation).
import itertools, random, numpy as np
from fractions import Fraction as F
A=np.load('/home/kevxhk/work/L-gct-210/stage2/r9/cand_D04_MAi_f2.npy').real
B=[[[int(round(A[q,i,l])) for l in range(5)] for i in range(4)] for q in range(5)]
def elem(c):
    M=[[F(1)]*5 for _ in range(5)]
    for i in range(4):
        for l in range(5): M[i+1][l]+=sum(c[q]*B[q][i][l] for q in range(5))
    return M
def perm(M):
    n=len(M)
    if n==0: return F(1)
    return sum(M[0][j]*perm([r[:j]+r[j+1:] for r in M[1:]]) for j in range(n) if M[0][j]!=0)
def minor(M,rows,cols): return [[M[i][j] for j in range(len(M)) if j not in cols] for i in range(len(M)) if i not in rows]
def rref_null(rows,n):
    M=[r[:] for r in rows]; piv=[]; rk=0
    for c in range(n):
        p=next((i for i in range(rk,len(M)) if M[i][c]!=0),None)
        if p is None: continue
        M[rk],M[p]=M[p],M[rk]; pv=M[rk][c]; M[rk]=[x/pv for x in M[rk]]
        for i in range(len(M)):
            if i!=rk and M[i][c]!=0:
                f=M[i][c]; M[i]=[x-f*y for x,y in zip(M[i],M[rk])]
        piv.append(c); rk+=1
    free=[c for c in range(n) if c not in piv]; basis=[]
    for fcol in free:
        v=[F(0)]*n; v[fcol]=F(1)
        for r,pc in enumerate(piv): v[pc]=-M[r][fcol]
        basis.append(v)
    return basis
def rank(rows,n): return n-len(rref_null(rows,n)) if rows else 0
random.seed(4)
rows=[]
for _ in range(40):
    c=[random.randint(-5,5) for _ in range(5)]; M=elem(c)
    rows.append([perm(minor(M,[i],[j])) for i in range(5) for j in range(5)])
Tb=rref_null(rows,25); dT=len(Tb)
print('dim T\' (contains T_1) =',dT,flush=True)
c0=[F(2),F(-1),F(3),F(1),F(-2)]; M0=elem(c0)
Q=[[F(0)]*25 for _ in range(25)]
for (i,j),(k,l) in itertools.product(itertools.product(range(5),range(5)),repeat=2):
    if i!=k and j!=l: Q[i*5+j][k*5+l]=perm(minor(M0,[i,k],[j,l]))
G=[[sum(Tb[a][x]*Q[x][y]*Tb[b][y] for x in range(25) for y in range(25) if Q[x][y]!=0) for b in range(dT)] for a in range(dT)]
rk=rank(G,dT); bound=dT-(rk+1)//2
# sanity: X inside T' and in the radical
print('rank q|T\' =',rk,' => FO2 bound',bound,'(every level space containing X has dim <=',bound,')',flush=True)
