# LM search: dim-k level spaces supported on rows 0..3 (row 4 zero) of 5x5; report free lines
import numpy as np, sys
sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases')
import level
from scipy.optimize import least_squares
k=int(sys.argv[1]); seed=int(sys.argv[2]); ntr=int(sys.argv[3]); NS=60
rng=np.random.default_rng(seed)
# ambient: 4x5 with total sum zero: 19-dim; basis
amb=[]
for i in range(4):
    for j in range(5):
        if (i,j)!=(3,4):
            t=np.zeros((5,5)); t[i,j]=1; t[3,4]=-1; amb.append(t.ravel())
amb=np.array(amb); Qa,_=np.linalg.qr(amb.T); A=Qa.T  # 19 x 25 orthonormal rows
D=A.shape[0]
Q,_=np.linalg.qr(rng.normal(size=(D,D))+1j*rng.normal(size=(D,D)))
S=rng.normal(size=(NS,k))+1j*rng.normal(size=(NS,k))
def resX(X):
    B=np.hstack([np.eye(k),X])@Q@A
    T=(S@B).reshape(-1,5,5); P=level.Pk(T)
    return P[:,2:5].ravel()
def res(x):
    m=k*(D-k); X=(x[:m]+1j*x[m:]).reshape(k,D-k); r=resX(X); return np.concatenate([r.real,r.imag])
for tr in range(ntr):
    x0=rng.normal(size=2*k*(D-k))*0.6
    sol=least_squares(res,x0,method='lm',max_nfev=6000,xtol=1e-15,ftol=1e-15,gtol=1e-15)
    m=k*(D-k); X=(sol.x[:m]+1j*sol.x[m:]).reshape(k,D-k)
    B=np.hstack([np.eye(k),X])@Q@A; U,s_,Vh=np.linalg.svd(B,full_matrices=False); Bo=Vh
    S2=rng.normal(size=(40,k))+1j*rng.normal(size=(40,k)); fr=abs(level.Pk((S2@Bo).reshape(-1,5,5))[:,1:]).max()
    print('k',k,'tr',tr,'cost %.2e fresh %.1e'%(sol.cost,fr),flush=True)
    if fr<1e-9: np.save('lv45_k%d_s%d_%d.npy'%(k,seed,tr),Bo)
