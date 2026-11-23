# try to find a DC 5x5 singular point of perm with ALL row and column norms = 1 (no zero line)
import numpy as np, itertools
from scipy.optimize import least_squares
n=5
C=[]
for i in range(n):
    r=np.zeros((n,n)); r[i,:]=1; C.append(r.ravel()); c=np.zeros((n,n)); c[:,i]=1; C.append(c.ravel())
D=np.linalg.svd(np.array(C))[2][9:].T
S4=list(itertools.permutations(range(4)))
def sp(A): return sum(A[0,p[0]]*A[1,p[1]]*A[2,p[2]]*A[3,p[3]] for p in S4)
def res(v):
    g=(D@(v[:16]+1j*v[16:])).reshape(n,n)
    r=np.array([sp(np.delete(np.delete(g,i,0),j,1)) for i in range(n) for j in range(n)])
    nr=(np.abs(g)**2).sum(1)-1; nc=((np.abs(g)**2).sum(0)-1)[:4]
    return np.concatenate([r.real,r.imag,nr,nc])
rng=np.random.default_rng(11); best=[]
for st in range(10):
    sol=least_squares(res,rng.normal(size=32)*0.4,method='lm',max_nfev=4000)
    best.append(np.linalg.norm(sol.fun))
print('CALIBRATION (col 4 free), 10 starts, sorted residuals:',np.round(sorted(best)[:8],5))
