# Exact check (rational arithmetic) of the model found in (N2-g):
#   Phi = (free column j=5 on all five rows) (+) D,  D = { d_c e_c q_c^T + d_d e_d q_d^T + d_e e_e q_e^T },
#   q_c = e_2 - e_3, q_d = e_1 - e_4, q_e = e_1 - e_2 - e_3 + e_4   (rows a,b,c,d,e = 0..4, columns 1..5 = 0..4).
# Claims: Phi (7-dim) is level; every hyperplane F of Phi of the form of (N2-a) satisfies the N2 identities (Qa),(Qb),(Q5 at J),(Q4).
import itertools, random
from fractions import Fraction as Fr
def perm(M):
    n=len(M); return sum(__import__('math').prod(M[i][p[i]] for i in range(n)) for p in itertools.permutations(range(n)))
q={2:[0,1,-1,0,0],3:[1,0,0,-1,0],4:[1,-1,-1,1,0]}
rnd=random.Random(5)
def elem():
    y=[Fr(rnd.randint(-5,5)) for _ in range(4)]; y.append(-sum(y))        # free column 5, sum zero
    d={i:Fr(rnd.randint(-5,5)) for i in (2,3,4)}
    t=[[Fr(0)]*5 for _ in range(5)]
    for r in range(5): t[r][4]=y[r]
    for i in (2,3,4):
        for j in range(5): t[i][j]+=d[i]*q[i][j]
    return t
ok=all(perm([[1+t[i][j] for j in range(5)] for i in range(5)])==120 for t in (elem() for _ in range(40)))
print('Phi level on 40 random rational points:',ok)
# planes P_i = span(e_5, q_i) (i = c,d,e), rho_a = rho_b = e_5
e5=[0,0,0,0,1]
def sub(rows,cols):
    k=len(rows); return sum(__import__('math').prod(rows[i][cols[p[i]]] for i in range(k)) for p in itertools.permutations(range(k)))
P={i:[e5,q[i]] for i in (2,3,4)}
Qb=all(sub([e5,P[2][a],P[3][b],P[4][c]],K)==0 for a in range(2) for b in range(2) for c in range(2) for K in itertools.combinations(range(5),4))
Q5J=all(sum(sub([P[2][a],P[3][b],P[4][c]],K) for K in itertools.combinations(range(5),3))==0 for a in range(2) for b in range(2) for c in range(2))
W=[[sub([P[2][a],P[3][b],P[4][c]],K) for K in itertools.combinations(range(5),3)] for a in range(2) for b in range(2) for c in range(2)]
import numpy as np
print('(Qb) rho P_c P_d P_e = 0 in A_4:',Qb,'  (Q5 at J):',Q5J,'  dim W =',np.linalg.matrix_rank(np.array(W,float)))
