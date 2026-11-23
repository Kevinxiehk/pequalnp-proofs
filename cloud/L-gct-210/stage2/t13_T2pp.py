# Exact verification of the three cubics used in the hand proof (T2'') [(1,2) Type I(C), (1,3) Type II with Q_3 = C].
# Gaussian integers as pairs; identities checked on a 5^4 integer grid (each variable has degree <= 3 < 5), both eps = +-1.
import itertools
def mul(x,y): return (x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0])
def add(*xs): return (sum(x[0] for x in xs), sum(x[1] for x in xs))
def g(x): return x if isinstance(x,tuple) else (x,0)
def perm3(M):
    M=[[g(x) for x in r] for r in M]; s=(0,0)
    for p in itertools.permutations(range(3)): s=add(s,mul(mul(M[0][p[0]],M[1][p[1]]),M[2][p[2]]))
    return s
bad={'B':0,'C':0,'D1':0,'A':0}
for eps in (1,-1):
    mi=(0,-eps)   # -eps*i
    for t,a1,a2,a3 in itertools.product(range(-2,3),repeat=4):
        # case B: S={p in C; q,s in Q_2}
        M=[[t,a1,-t-a1],[t,-a2,t+a2],[-t,a3,-t-a3]]
        if perm3(M)!=g(-2*t*(t*a1+a1*a2+a1*a3-a2*a3)): bad['B']+=1
        # case C: S={p in C; q in Q_1; s in Q_2}; row 3 = (-a3, -eps*i*(t-a3), -t)
        M=[[t,a1,-t-a1],[t,-a2,t+a2],[-a3,mul(mi,g(t-a3)),-t]]
        rhs=add(mul(g((a2-a1)*t),add(g(t),mul(mi,g(t-a3)))), g(-a3*(t*(a1+a2)+2*a1*a2)))
        if perm3(M)!=rhs: bad['C']+=1
        # case D1: S={p,p' in C; q in Q_2}; variables (t,x1,x2,x3)=(t,a1,a2,a3)
        x1,x2,x3=a1,a2,a3
        M=[[x1,t-x1,-t],[x2,t-x2,t],[-x3,-(t-x3),-t]]
        if perm3(M)!=g(-2*t*(t*x1-x1*x2-x1*x3+x2*x3)): bad['D1']+=1
        # case A (not needed): S={p in C; q,s in Q_1}: variables (b,a1,a2,a3) with t:=b
        b=t
        M=[[0,a1,-a1],[0,-a2,a2],[-b,mul(mi,g(a3)),mul((0,eps),g(b+a3))]]
        if perm3(M)!=g(-2*b*a1*a2): bad['A']+=1
print('violations of the cubic identities on the 5^4 grid (eps = +-1):',bad)
import numpy as np
print('Gram determinants: Q (cases B, T2):',round(np.linalg.det(np.array([[0,1,0,0],[1,0,1,1],[0,1,0,-1],[0,1,-1,0]]))),
      ' Q\' (case D1):',round(np.linalg.det(np.array([[0,1,0,0],[1,0,-1,-1],[0,-1,0,1],[0,-1,1,0]]))))
