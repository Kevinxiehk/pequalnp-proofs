import numpy as np, itertools, sys
from scipy.optimize import least_squares
n=5; calib=len(sys.argv)>1
C=[]
for i in range(n):
    r=np.zeros((n,n)); r[i,:]=1; C.append(r.ravel()); c=np.zeros((n,n)); c[:,i]=1; C.append(c.ravel())
D=np.linalg.svd(np.array(C))[2][9:].T
S4=list(itertools.permutations(range(4)))
def sp(A): return sum(A[0,p[0]]*A[1,p[1]]*A[2,p[2]]*A[3,p[3]] for p in S4)
rng=np.random.default_rng(5); lam=rng.normal(size=(n,n))+1j*rng.normal(size=(n,n)); mu=rng.normal(size=(n,n))+1j*rng.normal(size=(n,n))
def res(v):
    g=(D@(v[:16]+1j*v[16:])).reshape(n,n)
    r=[sp(np.delete(np.delete(g,i,0),j,1)) for i in range(n) for j in range(n)]
    r+=[lam[i]@g[i,:]-1 for i in range(n)]
    r+=[mu[j]@g[:,j]-1 for j in range(n if not calib else n-1)]
    r=np.array(r); return np.concatenate([r.real,r.imag])
best=[]
for st in range(20):
    sol=least_squares(res,rng.normal(size=32),method='lm',max_nfev=4000); best.append(np.linalg.norm(sol.fun))
    if best[-1]<1e-10:
        g=(D@(sol.x[:16]+1j*sol.x[16:])).reshape(n,n); print('  solution: row norms',np.round(np.linalg.norm(g,axis=1),3),'col norms',np.round(np.linalg.norm(g,axis=0),3))
print('calib' if calib else 'test','20 starts, best residuals',np.round(sorted(best)[:6],6))
