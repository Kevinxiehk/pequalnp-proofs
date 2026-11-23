# Lemma H: no 4x4 complex matrix with ALL entries nonzero has all sixteen 3x3 subpermanents zero.
# (hand proof via the V_4-Fourier argument: such a matrix would be D1 * Hadamard * D2, whose 3x3 subpermanents are +-2 r r r g g g.)
# Sanity: (i) 3x3 subpermanents of the 4x4 Hadamard matrix; (ii) Fourier lemma on random data; (iii) LM search: every converged
# solution of the 16 equations has a (numerically) zero entry.
import sys, itertools, numpy as np; sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
from pairlib import perm, rank
rng=np.random.default_rng(8)
def rnd(*k): return rng.normal(size=k)+1j*rng.normal(size=k)
H=np.array([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]])
vals=sorted(set(int(round(perm(H[list(I)][:,list(S)]))) for I in itertools.combinations(range(4),3) for S in itertools.combinations(range(4),3)))
print('(i) 3x3 subpermanents of the Hadamard matrix take the values',vals)
# (ii) kernel of multiplication by e on A_2 (4 variables) and the two-row annihilator lemma
pairs=list(itertools.combinations(range(4),2)); trip=list(itertools.combinations(range(4),3))
def mulmat(v):   # A_2 -> A_3
    M=np.zeros((4,6),complex)
    for a,t in enumerate(trip):
        for b,p in enumerate(pairs):
            if set(p)<set(t): M[a,b]=v[[j for j in t if j not in p][0]]
    return M
e=np.ones(4); K=np.linalg.svd(mulmat(e))[2][4:].conj().T
print('(ii) dim ker(e: A_2->A_3) =',6-rank(mulmat(e)),'; common kernel with a generic v:',6-rank(np.vstack([mulmat(e),mulmat(rnd(4))])),
      '; with v=(r,r2,r2,r) :',6-rank(np.vstack([mulmat(e),mulmat(np.array([1.3,0.4,0.4,1.3]))])))
# (iii) LM search
def F(x):
    G=x.reshape(4,4); return np.array([perm(G[list(I)][:,list(S)]) for I in itertools.combinations(range(4),3) for S in itertools.combinations(range(4),3)])
res=[]
for t in range(25):
    x=rnd(16); lam=1e-3
    for it in range(150):
        r=F(x); Jm=np.zeros((16,16),complex); h=1e-7
        for k in range(16):
            ee=np.zeros(16,complex); ee[k]=h; Jm[:,k]=(F(x+ee)-r)/h
        dx=np.linalg.lstsq(Jm.conj().T@Jm+lam*np.eye(16),-Jm.conj().T@r,rcond=None)[0]
        if np.linalg.norm(F(x+dx))<np.linalg.norm(r): x=x+dx; lam=max(lam/3,1e-13)
        else: lam*=5
        if np.linalg.norm(r)<1e-13: break
    res.append((np.linalg.norm(F(x)),np.abs(x).min()/np.abs(x).max()))
conv=[r for r in res if r[0]<1e-9]
print('(iii) LM: %d of %d runs converged; largest (min|entry|/max|entry|) among converged: %.1e'%(len(conv),len(res),max(r[1] for r in conv) if conv else -1))
