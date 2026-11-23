# sample DC g with P_2..P_5(g)=0 and all 4x4 subpermanents = 0; inspect support / structure
import numpy as np, itertools
from scipy.optimize import least_squares
n=5
C=[]
for i in range(n):
    r=np.zeros((n,n)); r[i,:]=1; C.append(r.ravel()); c=np.zeros((n,n)); c[:,i]=1; C.append(c.ravel())
D=np.linalg.svd(np.array(C))[2][9:].T   # 25x16 real orthonormal DC basis
S4=list(itertools.permutations(range(4))); S3=list(itertools.permutations(range(3))); S2=[(0,1),(1,0)]
R4=list(itertools.combinations(range(5),4)); R3=list(itertools.combinations(range(5),3)); R2=list(itertools.combinations(range(5),2))
def sp(A,PP): return sum(np.prod([A[a,p[a]] for a in range(len(p))]) for p in PP)
def Pk(g,k,RR,PP): return sum(sp(g[np.ix_(R,Cc)],PP) for R in RR for Cc in RR)
def res(v):
    x=v[:16]+1j*v[16:]; g=(D@x).reshape(n,n)
    r=[]
    r+= [sp(g[np.ix_(R,Cc)],S4) for R in R4 for Cc in R4]
    r.append(np.vdot(x,x).real-1+0j)
    r=np.array(r); return np.concatenate([r.real,r.imag])
rng=np.random.default_rng(7); found=0
for st in range(14):
    sol=least_squares(res,rng.normal(size=32),method='lm',max_nfev=3000)
    if np.linalg.norm(sol.fun)<1e-10:
        found+=1; g=(D@(sol.x[:16]+1j*sol.x[16:])).reshape(n,n); a=np.abs(g)
        rows=(a.max(1)>1e-6).sum(); cols=(a.max(0)>1e-6).sum()
        s3=max(abs(sp(g[np.ix_(R,Cc)],S3)) for R in R3 for Cc in R3)
        print('sol %2d: nonzero rows %d cols %d rank %d max|3x3| %.1e  min|row norm| %.1e min|col norm| %.1e'%(st,rows,cols,np.linalg.matrix_rank(g,1e-7),s3,np.linalg.norm(g,axis=1).min(),np.linalg.norm(g,axis=0).min()),flush=True)
print('found',found,'of 14')
