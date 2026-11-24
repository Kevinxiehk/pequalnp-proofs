# verify2: stage2's space M* (R4-4): exact level check (polynomial identity) and the first-order extension space T_1(M*) (R4-6).
import itertools, sys, random, importlib.util
from fractions import Fraction as Fr
spec=importlib.util.spec_from_file_location('ex7','/home/kevxhk/work/L-gct-210/rows/exact7.py'); ex7=importlib.util.module_from_spec(spec); spec.loader.exec_module(ex7)
a,b,c,d,e=0,1,2,3,4
def Mstar(ma,mb,al,be,ga):
    Z=lambda:[[0]*5 for _ in range(5)]
    g1=Z(); g1[a][0]=-1; g1[c][0]=1; g1[c][1]=ma*al; g1[c][4]=-ma*al
    g2=Z(); g2[b][0]=-1; g2[c][0]=1; g2[c][1]=mb*al; g2[c][4]=-mb*al
    g3=Z(); g3[c][0]=1; g3[d][0]=-1
    g4=Z(); g4[c][0]=1; g4[e][0]=-1
    g5=Z(); g5[c][1]=al; g5[c][4]=-al; g5[d][1]=-be; g5[d][2]=be; g5[d][3]=be; g5[d][4]=-be
    g6=Z(); g6[c][1]=al; g6[c][4]=-al; g6[e][2]=-ga; g6[e][3]=ga
    return [g1,g2,g3,g4,g5,g6]
def perm(M):
    n=len(M)
    if n==1: return M[0][0]
    return sum(M[0][j]*perm([r[:j]+r[j+1:] for r in M[1:]]) for j in range(n) if M[0][j]!=0)
def cof(M): return [perm([[M[i][j] for j in range(5) if j!=jj] for i in range(5) if i!=ii]) for ii in range(5) for jj in range(5)]
def T1dim(B,npts=45,seed=1):
    rnd=random.Random(seed); rows=[]
    for _ in range(npts):
        x=[rnd.randint(-4,4) for _ in B]
        M=[[1+sum(x[k]*B[k][i][j] for k in range(len(B))) for j in range(5)] for i in range(5)]
        rows.append(cof(M))
    return 25-ex7.rank(rows)
for par in [(1,2,1,1,1),(2,-3,1,2,5),(1,1,1,1,1),(1,-1,2,3,7),(0,1,1,1,1),(0,0,1,1,1),(3,5,-2,7,1),(1,2,1,-1,1),(Fr(1,2),Fr(-2,3),Fr(5,7),3,Fr(1,3))]:
    B=Mstar(*par); dim=ex7.rank([[M[i][j] for i in range(5) for j in range(5)] for M in B])
    const,rest=ex7.level_identity(B)
    # single-column elements of column 0 inside M*
    print('parameters',tuple(str(p) for p in par),': dim M* =',dim,'; perm(J+m) = %s + (%d nonzero non-constant coefficients)'%(const,len(rest)),'; dim T_1(M*) =',T1dim(B),flush=True)
