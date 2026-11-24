# verify2 r11: (1) per-j cubic condition T_j = kappa * b(sigma - g_j, 3 sigma o sigma + 2 g_j o g_j - R) as a POLYNOMIAL identity
# (random sum-zero vectors g_k with sum g_k = 3 sigma, y_k = (sigma - g_k)/2); (2) summed identity on genuine strongly level 3-spaces.
import numpy as np, itertools, glob
rng=np.random.default_rng(1)
def rv():
    x=rng.normal(size=4)+1j*rng.normal(size=4); return x-x.mean()
b=lambda x,y: (x*y).sum()
for trial in range(3):
    sig=rv(); g=[rv() for _ in range(4)]; g.append(3*sig-sum(g))
    y=[(sig-gk)/2 for gk in g]
    R=sum(gk*gk for gk in g)
    for j in range(5):
        cols=[y[k] for k in range(5) if k!=j]
        T=sum((cols[a]*cols[b_]*cols[c]).sum() for a,b_,c in itertools.combinations(range(4),3))
        F=b(sig-g[j],3*sig*sig+2*g[j]*g[j]-R)
        print('trial',trial,'j',j,'T_j / F =',np.round(T/F,10))
# (2) genuine spaces
H=np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],dtype=float)
files=sorted(glob.glob('/home/kevxhk/work/L-gct-210/rows/sl3_s1*.npy'))[:6]
for f in files:
    K=np.load(f)   # 3 x 4 x 5, strongly level, s(K) = V
    S=np.array([k.sum(axis=1) for k in K])          # row sums (3 x 4)
    for _ in range(2):
        a=rng.normal(size=3)+1j*rng.normal(size=3); Y=np.tensordot(a,K,1); sig=Y.sum(axis=1)
        g=[sig-2*Y[:,k] for k in range(5)]
        lhs=sum((gk**3).sum() for gk in g); rhs=3*(sig**3).sum()
        print(f.split('/')[-1],'sum c(g_j) - 3 c(sigma) =',abs(lhs-rhs),' |c(sigma)| =',abs(rhs))
