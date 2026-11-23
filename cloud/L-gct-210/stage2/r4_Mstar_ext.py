# First-order extension space of M*: T_1 = {t : sum_ij t_ij perm_4((J+m)^(ij)) = 0 for all m in M*}. Every level space containing M* lies
# in T_1 (perm(J + m + eps t) = 120 for t in L, m in M*). If dim T_1 <= 8, M* lies in no 9-dim level space.
import itertools, sys, random
import numpy as np
from fractions import Fraction
sys.path.insert(0,'/home/claude/work/L-gct-210/stage2'); import exactla
P4=list(itertools.permutations(range(4)))
def perm4(M): return sum(M[0][p[0]]*M[1][p[1]]*M[2][p[2]]*M[3][p[3]] for p in P4)
def cof(M): return [perm4([[M[r][c] for c in range(5) if c!=j] for r in range(5) if r!=i]) for i in range(5) for j in range(5)]
def rowvec(i,v): return [[v[j] if r==i else 0 for j in range(5)] for r in range(5)]
def add(*Ms): return [[sum(M[i][j] for M in Ms) for j in range(5)] for i in range(5)]
def E(i,j,v=1):
    M=[[0]*5 for _ in range(5)]; M[i][j]=v; return M
def Mstar(ma,mb,al,be,ga):
    a,b,c,d,e=0,1,2,3,4; Xc=[0,al,0,0,-al]; Xd=[0,be,-be,-be,be]; Xe=[0,0,ga,-ga,0]
    return [add(rowvec(a,[-1,0,0,0,0]),rowvec(c,[1]+[ma*x for x in Xc[1:]])), add(rowvec(b,[-1,0,0,0,0]),rowvec(c,[1]+[mb*x for x in Xc[1:]])),
            add(E(c,0),E(d,0,-1)), add(E(c,0),E(e,0,-1)), add(rowvec(c,Xc),rowvec(d,[-x for x in Xd])), add(rowvec(c,Xc),rowvec(e,[-x for x in Xe]))]
random.seed(3)
def rank_exact(rows):
    R=exactla.rref([[Fraction(x) for x in r] for r in rows]); R=R[0] if isinstance(R,tuple) else R
    return sum(1 for r in R if any(x!=0 for x in r))
for (ma,mb,al,be,ga) in ((1,2,1,1,1),(1,-1,1,1,1),(1,1,1,1,1),(0,1,1,1,1),(0,0,1,1,1),(2,5,3,-2,7),(1,3,2,1,-1)):
    basis=Mstar(ma,mb,al,be,ga); rows=[]
    for trial in range(60):
        co=[random.randint(-4,4) for _ in range(6)]; M=[[1+sum(co[k]*basis[k][i][j] for k in range(6)) for j in range(5)] for i in range(5)]
        rows.append(cof(M))
    A=np.array(rows,dtype=float); s=np.linalg.svd(A,compute_uv=False); rk=int((s>1e-7*s[0]).sum())
    dimM=np.linalg.matrix_rank(np.array(basis,dtype=float).reshape(6,25))
    print('m_a,m_b,al,be,ga =',(ma,mb,al,be,ga),' dim M* =',dimM,' rank of the cofactor span (float) =',rk,' => dim T_1 =',25-rk,flush=True)
# exact rank for the first parameter set
basis=Mstar(1,2,1,1,1); rows=[]
for trial in range(40):
    co=[random.randint(-3,3) for _ in range(6)]; M=[[1+sum(co[k]*basis[k][i][j] for k in range(6)) for j in range(5)] for i in range(5)]
    rows.append(cof(M))
try:
    print('exact rank (Fractions, 40 points) for (1,2,1,1,1):',rank_exact(rows))
except Exception as ex: print('exact rank routine failed:',ex)
