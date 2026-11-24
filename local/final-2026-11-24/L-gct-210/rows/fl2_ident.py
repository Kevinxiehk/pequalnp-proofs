"""Exact (Fraction) checks of the identities used in Theorem FL2-gen (rows i = 3, r = 4; 3-row part Y'' = rows 0..2)."""
import itertools, random
from fractions import Fraction as Fr
from math import prod
def perm(M):
    n=len(M); return sum(prod(M[i][p[i]] for i in range(n)) for p in itertools.permutations(range(n)))
def Delta(Y3,t=1):
    X=[[1+t*y for y in row] for row in Y3]; D=[[Fr(0)]*5 for _ in range(5)]
    for j,k in itertools.combinations(range(5),2):
        cols=[c for c in range(5) if c not in (j,k)]; D[j][k]=D[k][j]=perm([[X[i][c] for c in cols] for i in range(3)])
    return D
random.seed(3)
Y3=[[Fr(random.randint(-4,4)) for _ in range(5)] for _ in range(3)]
a=[Fr(random.randint(-4,4)) for _ in range(5)]; b=[Fr(random.randint(-4,4)) for _ in range(5)]
# (c) perm(J+z) = (1+b)^T Delta(Y'') (1+a)
Z=[[1+y for y in row] for row in Y3]+[[1+x for x in a],[1+x for x in b]]
D=Delta(Y3); lhs=perm(Z); rhs=sum((1+b[j])*D[j][k]*(1+a[k]) for j in range(5) for k in range(5))
print('(c) perm(J+z) = (1+z_r)^T Delta(z\'\') (1+z_i):',lhs==rhs)
# (a),(b): linear part Delta_1 = d/dt Delta(tY'') at 0 via exact finite difference of a cubic polynomial: use interpolation at t=0,1,-1,2
def lin(f):   # coefficient of t in a cubic polynomial f(t) from values at -1,0,1,2
    v={t:f(t) for t in (-1,0,1,2)}
    # f = c0 + c1 t + c2 t^2 + c3 t^3 ; solve
    c0=v[0]; c2=(v[1]+v[-1])/2-c0; s=(v[1]-v[-1])/2   # s = c1 + c3
    c3=(v[2]-c0-4*c2-2*s)/6; return s-c3
D1=[[lin(lambda t:Delta(Y3,Fr(t))[j][k]) for k in range(5)] for j in range(5)]
c=[sum(Y3[i][j] for i in range(3)) for j in range(5)]; S=sum(c)
u=[Fr(random.randint(-4,4)) for _ in range(5)]; m=sum(u)/5; u=[x-m for x in u]
lhsv=[sum(D1[j][k]*u[k] for k in range(5)) for j in range(5)]; cu=sum(x*y for x,y in zip(c,u))
rhsv=[-2*S*u[j]+4*c[j]*u[j]-2*cu for j in range(5)]
print('(a) Delta_1 u = -2S u + 4 c o u - 2 (c.u) 1  (sum u = 0):',lhsv==rhsv)
print('(b) Delta_1 1 = 6S 1 - 6c:',[sum(D1[j]) for j in range(5)]==[6*S-6*c[j] for j in range(5)],'; Delta_0 = 6(J-I):',all(Delta(Y3,0)[j][k]==(6 if j!=k else 0) for j in range(5) for k in range(5)))
D0=Delta(Y3,0); print('(d) 1^T Delta(Y\'\') 1 = 2 N_{3x5}(J+Y\'\'):',sum(map(sum,D))==2*sum(prod(1+Y3[i][f[i]] for i in range(3)) for f in itertools.permutations(range(5),3)))
