# verify2 r11: stage2 R11-3: q_{s e_i w^T}(t,t) = 12 P_2(t) + s * 4 sum_j w_j P_2(t^(i) without column j)   (sum w = 0), q = D^2 perm(J + m)(t,t)
import numpy as np, itertools
rng=np.random.default_rng(7)
def perm(M):
    n=M.shape[0]; return sum(np.prod([M[r,p[r]] for r in range(n)]) for p in itertools.permutations(range(n)))
def P2(M):
    return sum(M[a,c]*M[b,d]+M[a,d]*M[b,c] for a,b in itertools.combinations(range(M.shape[0]),2) for c,d in itertools.combinations(range(M.shape[1]),2))
def hess(A,T):   # second derivative d^2/de^2 perm(A + e T) at e = 0 (polynomial: exact via 3-point finite differences of a degree-5 poly -> use 6 points)
    es=np.arange(-3,3).astype(float); vals=[perm(A+e*T) for e in es]
    c=np.polyfit(es,vals,5); return 2*c[-3]
for trial in range(3):
    i=rng.integers(5); w=rng.normal(size=5); w-=w.mean(); s=rng.normal(); T=rng.normal(size=(5,5))
    J=np.ones((5,5)); m=np.zeros((5,5)); m[i]=s*w
    lhs=hess(J+m,T)
    Ti=np.delete(T,i,axis=0)
    rhs=12*P2(T)+s*4*sum(w[j]*P2(np.delete(Ti,j,axis=1)) for j in range(5))
    print('i',i,' q_m(t,t) =',round(lhs,8),'  12 P2 + s Bw =',round(rhs,8), ' 2*q0 check:', round(hess(J,T),8), round(12*P2(T),8))
