# LM: dim-k level spaces supported on rows 0..2, cols 0..3 of 5x5 (3x4 level); Grassmannian chart, analytic-free FD
import numpy as np, sys
sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases'); import level
from scipy.optimize import least_squares
k=int(sys.argv[1]); seed=int(sys.argv[2]); ntr=int(sys.argv[3]); NS=40
rng=np.random.default_rng(seed)
amb=[]
for i in range(3):
    for j in range(4):
        if (i,j)!=(2,3):
            t=np.zeros((5,5)); t[i,j]=1; t[2,3]=-1; amb.append(t.ravel())
A=np.linalg.qr(np.array(amb).T)[0].T; D=len(A)
Q,_=np.linalg.qr(rng.normal(size=(D,D))+1j*rng.normal(size=(D,D)))
S=rng.normal(size=(NS,k))+1j*rng.normal(size=(NS,k))
def res(x):
    m=k*(D-k); X=(x[:m]+1j*x[m:]).reshape(k,D-k); B=np.hstack([np.eye(k),X])@Q@A
    r=level.Pk((S@B).reshape(-1,5,5))[:,2:4].ravel(); return np.concatenate([r.real,r.imag])
for tr in range(ntr):
    sol=least_squares(res,rng.normal(size=2*k*(D-k))*0.6,method='lm',max_nfev=5000,xtol=1e-15,ftol=1e-15,gtol=1e-15)
    m=k*(D-k); X=(sol.x[:m]+1j*sol.x[m:]).reshape(k,D-k); B=np.hstack([np.eye(k),X])@Q@A
    Bo=np.linalg.svd(B,full_matrices=False)[2]; S2=rng.normal(size=(30,k))+1j*rng.normal(size=(30,k))
    fr=abs(level.Pk((S2@Bo).reshape(-1,5,5))[:,1:]).max()
    print('3x4 k',k,'tr',tr,'cost %.1e fresh %.1e'%(sol.cost,fr),flush=True)
