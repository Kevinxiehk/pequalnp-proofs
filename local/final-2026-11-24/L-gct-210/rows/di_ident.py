"""Exact (Fraction) checks of the identities used in section DI.
 (I1) deletion formula: for a k x q matrix X (k <= q-1), N_j(X) := sum over injections rows -> columns != j of prod X_{i f(i)}
      equals  sum_{S subset rows} (-1)^{|S|} |S|! N^{(rows - S)}(X) prod_{i in S} X_ij   (N^{(R)} = injection sum of rows R, all columns).
 (I2) row-centred 3 x q: P_2 = -sum_j e_2(col j), P_3 = 2 sum_j e_3(col j).
 (I3) row sums 0 and pairwise orthogonal rows, 4 x q: P_4 = -6 sum_j e_4(col j);
      deletion vectors p_1 = -e_1^col, p_2 = 2 e_2^col, p_3 = -6 e_3^col + P_3,  p_4 = 24 e_4^col - 6 beta_1234 - 2 sum_i beta_{R-i} y_i."""
import itertools, random
from fractions import Fraction as Fr
def N(X,rows,cols):
    return sum(__import__('math').prod(X[i][f[a]] for a,i in enumerate(rows)) for f in itertools.permutations(cols,len(rows)))
def Pk(Y,k,cols=None):
    p=len(Y); q=len(Y[0]); cols=list(range(q)) if cols is None else cols; s=0
    for R in itertools.combinations(range(p),k):
        for C in itertools.combinations(cols,k):
            s+=N(Y,R,C)   # N over exactly these k columns = permanent
    return s
def esym(v,k): return sum(__import__('math').prod(c) for c in itertools.combinations(v,k))
random.seed(1); fact=__import__('math').factorial
# (I1)
for (k,q) in ((2,5),(3,5),(4,5)):
    X=[[Fr(random.randint(-5,5)) for _ in range(q)] for _ in range(k)]
    ok=True
    for j in range(q):
        lhs=N(X,list(range(k)),[c for c in range(q) if c!=j]); rhs=0
        for r in range(k+1):
            for S in itertools.combinations(range(k),r):
                rest=[i for i in range(k) if i not in S]
                rhs+=(-1)**r*fact(r)*N(X,rest,list(range(q)))*__import__('math').prod(X[i][j] for i in S)
        ok&=(lhs==rhs)
    print('(I1) k=%d q=%d:'%(k,q),ok)
def centre_rows(Y): return [[x-sum(r)/len(r) for x in r] for r in Y]
# (I2)
Y=centre_rows([[Fr(random.randint(-5,5)) for _ in range(6)] for _ in range(3)])
cols=[[Y[i][j] for i in range(3)] for j in range(6)]
print('(I2):',Pk(Y,2)==-sum(esym(c,2) for c in cols), Pk(Y,3)==2*sum(esym(c,3) for c in cols))
# (I3): build 4 x 7 with row sums 0 and pairwise orthogonal rows (rational Gram-Schmidt inside 1^perp, bilinear form)
q=7; rows=[]
while len(rows)<4:
    v=[Fr(random.randint(-4,4)) for _ in range(q)]; m=sum(v)/q; v=[x-m for x in v]
    for r in rows:
        rr=sum(a*a for a in r); c=sum(a*b for a,b in zip(v,r))/rr; v=[a-c*b for a,b in zip(v,r)]
    if any(v): rows.append(v)
Y=rows; cols=[[Y[i][j] for i in range(4)] for j in range(q)]
beta=lambda B: sum(__import__('math').prod(Y[i][j] for i in B) for j in range(q))
print('(I3) P_4 = -6 sum e_4:',Pk(Y,4)==-6*sum(esym(c,4) for c in cols), ' P_2 = 0:',Pk(Y,2)==0,' P_3 = 2 sum e_3:',Pk(Y,3)==2*sum(esym(c,3) for c in cols))
ok=[True]*4
for j in range(q):
    cj=[c for c in range(q) if c!=j]
    ok[0]&=(Pk(Y,1,cj)==-esym(cols[j],1)); ok[1]&=(Pk(Y,2,cj)==2*esym(cols[j],2))
    ok[2]&=(Pk(Y,3,cj)==-6*esym(cols[j],3)+Pk(Y,3))
    ok[3]&=(Pk(Y,4,cj)==24*esym(cols[j],4)-6*beta([0,1,2,3])-2*sum(beta([a for a in range(4) if a!=i])*Y[i][j] for i in range(4)))
print('(I3) deletion vectors p_1..p_4:',ok)
