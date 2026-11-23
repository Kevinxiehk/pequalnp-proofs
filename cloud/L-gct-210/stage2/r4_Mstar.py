# Explicit N2-shaped 6-dim space M* (block (alpha3)): exact integer check of perm(J + m) = 120 on M* (polynomial identity tested on
# integer points with Fractions-free integer arithmetic), the conditions (Z2) on L_a, L_b, and invariants.
import itertools, random, sys
import numpy as np
sys.path.insert(0,'/home/claude/work/L-gct-210/stage2'); from pairlib import rank
def E(i,j,v=1):
    M=[[0]*5 for _ in range(5)]; M[i][j]=v; return M
def add(*Ms): return [[sum(M[i][j] for M in Ms) for j in range(5)] for i in range(5)]
def sc(c,M): return [[c*x for x in r] for r in M]
def rowvec(i,v): return [[v[j] if r==i else 0 for j in range(5)] for r in range(5)]
def perm(M):
    n=len(M); tot=0
    for p in itertools.permutations(range(n)):
        t=1
        for i in range(n): t*=M[i][p[i]]
        tot+=t
    return tot
a,b,c,d,e=0,1,2,3,4; ma,mb=1,2; al,be,ga=1,1,1
Xc=[0,al,0,0,-al]; Xd=[0,be,-be,-be,be]; Xe=[0,0,ga,-ga,0]
basis=[ add(rowvec(a,[-1,0,0,0,0]), rowvec(c,[1]+[ma*x for x in Xc[1:]])),       # x^{ac}
        add(rowvec(b,[-1,0,0,0,0]), rowvec(c,[1]+[mb*x for x in Xc[1:]])),       # x^{bc}
        add(E(c,0),E(d,0,-1)), add(E(c,0),E(e,0,-1)),                            # dominoes of column 0
        add(rowvec(c,Xc),rowvec(d,[-x for x in Xd])), add(rowvec(c,Xc),rowvec(e,[-x for x in Xe])) ]
random.seed(1); bad=0
for trial in range(400):
    co=[random.randint(-6,6) for _ in range(6)]; M=[[1+sum(co[k]*basis[k][i][j] for k in range(6)) for j in range(5)] for i in range(5)]
    if perm(M)!=120: bad+=1
print('perm(J+m) = 120 on M*: violations',bad,'of 400 integer points  (a degree-5 polynomial in 6 variables vanishing on a 13^6 grid sample)')
B=np.array(basis,dtype=float); print('dim M* =',rank(B.reshape(6,-1)))
# (Z2): L_a = {m in M*: row a = 0}: coefficient of x^{ac} zero; all 4x4 subperms of rows b,c,d,e vanish
for row,drop in ((a,0),(b,1)):
    bad=0
    for trial in range(200):
        co=[random.randint(-6,6) for _ in range(6)]; co[drop]=0
        M=[[sum(co[k]*basis[k][i][j] for k in range(6)) for j in range(5)] for i in range(5) if i!=row]
        for j in range(5):
            if perm([[r[l] for l in range(5) if l!=j] for r in M])!=0: bad+=1
    print('(Z2) on L_%s: violations'%'ab'[row],bad)
print('single-column dims per column:',[6-rank(np.delete(B,j,axis=2).reshape(6,-1)) for j in range(5)],' single-row dims per row:',[6-rank(np.delete(B,i,axis=1).reshape(6,-1)) for i in range(5)])
print('row projection dims:',[rank(B[:,i,:]) for i in range(5)],' column projection dims:',[rank(B[:,:,j]) for j in range(5)])
print('lam_{rr\'} within M*:',[[6-rank(B[:,[r,s],:].reshape(6,-1)) for s in range(5)] for r in range(5)])
