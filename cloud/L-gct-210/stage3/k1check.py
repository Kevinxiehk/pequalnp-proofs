# Exact check of (K1): for a 2-plane P of C^5, K(P) = {Q in A_2 : Q y = 0 in A_3 for all y in P} has dim <= 1; and (G2): {y : Q y = 0} has dim <= 2.
import itertools, random
from fractions import Fraction as Fr
import sys; sys.path.insert(0,"/home/claude/work/L-gct-210/stage3")
from kcheck import rank, PAIRS, IDX
TR=list(itertools.combinations(range(5),3))
def KP(P):
    rows=[]
    for y in P:
        for K in TR:
            r=[Fr(0)]*10
            for m in K:
                p=tuple(c for c in K if c!=m); r[IDX[p]]+=y[m]
            rows.append(r)
    return 10-rank(rows)
rnd=random.Random(1); cnt={}
for trial in range(3000):
    supp=[rnd.sample(range(5),rnd.randint(1,5)) for _ in range(2)]
    P=[[Fr(rnd.choice([-3,-2,-1,1,2,3])) if j in s else Fr(0) for j in range(5)] for s in supp]
    if rank([P[0][:],P[1][:]])<2: continue
    k=KP(P); cnt[k]=cnt.get(k,0)+1
print('(K1) dim K(P) over random 2-planes with random supports:',cnt)
cnt={}
for trial in range(3000):
    Q=[Fr(rnd.choice([-2,-1,0,0,0,1,2])) for _ in range(10)]
    if not any(Q): continue
    rows=[]
    for K in TR:
        r=[Fr(0)]*5
        for m in K:
            p=tuple(c for c in K if c!=m); r[m]+=Q[IDX[p]]
        rows.append(r)
    d=5-rank(rows); cnt[d]=cnt.get(d,0)+1
print('(G2) dim {y : Q y = 0} over random nonzero Q:',cnt)
