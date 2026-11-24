# (Z5) exploration: strongly level 4x5 Y with ZERO row sum and 5 nonzero columns.  Degree 2 => columns isotropic: y_k = la_k c(t_k).
# Necessary: P_4 for each deletion j: perm[H c(t_a)]_{a != j} = 0 (la != 0) -- 5 equations in the 5 points alone.
# Newton (least squares, complex) from random starts on these 5 equations; report solutions, then test the cubic + linear conditions.
import itertools, numpy as np, random
H=np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],dtype=complex)
def c(s): return np.array([s*s-1, 1j*(s*s+1), 2*s])
def perm(M): return sum(np.prod([M[i][s[i]] for i in range(4)]) for s in itertools.permutations(range(4)))
def F(t):
    cols=[H@c(x) for x in t]
    return np.array([perm(np.array([cols[a] for a in range(5) if a!=j]).T) for j in range(5)])
def J(t,h=1e-7):
    f0=F(t); return np.array([(F(t+h*np.eye(5)[k])-f0)/h for k in range(5)]).T
random.seed(5); sols=[]
for st in range(300):
    t=np.array([complex(random.gauss(0,1.2),random.gauss(0,1.2)) for _ in range(5)])
    for it in range(60):
        f=F(t)
        if np.abs(f).max()<1e-11: break
        try: d=np.linalg.lstsq(J(t),-f,rcond=None)[0]
        except Exception: break
        t=t+d
        if np.abs(t).max()>1e4: break
    if np.abs(F(t)).max()<1e-9 and np.abs(t).max()<1e4:
        dmin=min(abs(a-b) for a,b in itertools.combinations(t,2))
        sols.append((dmin,t))
print('P4-only: converged',len(sols),'of 300; with distinct points:',sum(1 for d,_ in sols if d>1e-5))
for d,t in sols[:6]: print('  min dist %.2e'%d, np.round(t,5))
