# t = [[U,-U],[-U,U]] (2p x 2p).  Compare M_k(t) with Q_j(U) = sum_{|R|=|C|=j} perm(U[R,C])^2.
import numpy as np, itertools
rng = np.random.default_rng(2)
def Mk(t):
    a, c = t.shape; G = np.zeros(1<<a, complex); G[0] = 1
    for j in range(c):
        Gn = G.copy()
        for m in range(1<<a):
            for i in range(a):
                if not m>>i&1: Gn[m|1<<i] += G[m]*t[i,j]
        G = Gn
    pc = [bin(m).count('1') for m in range(1<<a)]
    return [sum(G[m] for m in range(1<<a) if pc[m]==k) for k in range(1,a+1)]
def perm(A):
    k = A.shape[0]
    return sum(np.prod([A[i,s[i]] for i in range(k)]) for s in itertools.permutations(range(k))) if k else 1
def Q(U,j):
    p = U.shape[0]
    return sum(perm(U[np.ix_(R,C)])**2 for R in itertools.combinations(range(p),j) for C in itertools.combinations(range(p),j))
for p in [2,3]:
    U = rng.standard_normal((p,p))+1j*rng.standard_normal((p,p))
    t = np.block([[U,-U],[-U,U]])
    M = Mk(t)
    print(p, 'M_k:', [np.round(x,6) for x in M])
    print(p, 'Q_j:', [np.round(Q(U,j),6) for j in range(1,p+1)])
    print(p, 'ratios M_2j/Q_j:', [np.round(M[2*j-1]/Q(U,j),6) for j in range(1,p+1)])
