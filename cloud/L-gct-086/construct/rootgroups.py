# Check: a x (N*G) matrix with column groups zeta^l u_g (l=0..N-1), N > a/2:
# sum_k M_k z^k = 1 - (-1)^N N! z^N sum_g e_N(u_g).  (exact identity; numeric spot check here)
import numpy as np, itertools, math
rng = np.random.default_rng(1)
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
def eN(u,N): return sum(np.prod(c) for c in itertools.combinations(u,N))
for a, N, G in [(4,3,2),(5,3,3),(6,4,2),(4,2,2)]:
    z = np.exp(2j*np.pi/N); U = rng.standard_normal((G,a))+1j*rng.standard_normal((G,a))
    t = np.concatenate([np.outer(U[g], [z**l for l in range(N)]) for g in range(G)], 1)
    pred = -(-1)**N*math.factorial(N)*sum(eN(U[g],N) for g in range(G))
    print(a,N,G,'2N>a' if 2*N>a else '2N<=a', np.round(Mk(t),8), 'pred M_N', np.round(pred,8))
