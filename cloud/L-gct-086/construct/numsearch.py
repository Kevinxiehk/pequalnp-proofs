# Numerical search: does an a x c (rectangular) level space of dimension d exist?
# Level: all injective sums M_k (k=1..min(a,c)) vanish on L.  Grassmannian chart V=[I|W] (permuted).
import numpy as np, sys
from scipy.optimize import least_squares
rng = np.random.default_rng(int(sys.argv[5]) if len(sys.argv)>5 else 0)
a, c, d = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
tries = int(sys.argv[4]) if len(sys.argv)>4 else 5
N = a*c
from math import comb
S = int(1.1*comb(d+min(a,c)-1, min(a,c))) + 10
X = (rng.standard_normal((S,d)) + 1j*rng.standard_normal((S,d)))/np.sqrt(2)
pc = np.array([bin(m).count('1') for m in range(1<<a)])
IDX = [(np.array([m for m in range(1<<a) if not m>>i&1]), np.array([m|(1<<i) for m in range(1<<a) if not m>>i&1])) for i in range(a)]
def Mk(T):  # T: S x a x c ; returns S x a array of M_1..M_a (rows a <= c assumed)
    Sx = T.shape[0]
    G = np.zeros((Sx, 1<<a), complex); G[:,0] = 1
    for j in range(c):
        Gn = G.copy()
        for i in range(a):
            src, dst = IDX[i]
            Gn[:, dst] += G[:, src] * T[:, i, j][:,None]
        G = Gn
    return np.stack([G[:, pc==k].sum(1) for k in range(1, a+1)], 1)
def resid(w, perm):
    W = (w[:len(w)//2] + 1j*w[len(w)//2:]).reshape(d, N-d)
    V = np.zeros((d, N), complex); V[:, perm[:d]] = np.eye(d); V[:, perm[d:]] = W
    T = (X @ V).reshape(S, a, c)
    r = Mk(T).ravel()
    return np.concatenate([r.real, r.imag])
best = 1e9
for tr in range(tries):
    perm = rng.permutation(N)
    w0 = rng.standard_normal(2*d*(N-d))*0.5
    sol = least_squares(resid, w0, args=(perm,), method='lm', max_nfev=4000, xtol=1e-15, ftol=1e-15, gtol=1e-15)
    best = min(best, sol.cost)
    print(f"a={a} c={c} d={d} try {tr}: cost {sol.cost:.3e}", flush=True)
    if sol.cost < 1e-18: break
print("BEST", a, c, d, best)
