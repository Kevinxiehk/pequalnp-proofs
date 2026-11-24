# search strongly level 4x5 spaces L' (all 4x4 column deletions level), dim k
import numpy as np, itertools, sys
from scipy.optimize import least_squares
k=int(sys.argv[1]); seed=int(sys.argv[2]); NS=int(sys.argv[3]) if len(sys.argv)>3 else 80
rng=np.random.default_rng(seed)
# basis of V4 (sum zero in C^4)
E=np.array([[1,-1,0,0],[0,1,-1,0],[0,0,1,-1]],float).T  # 4x3
def emb(c):  # c (...,15) -> (...,4,5)
    c=c.reshape(c.shape[:-1]+(5,3)); return np.einsum('ia,...ja->...ij',E,c)
Q,_=np.linalg.qr(rng.normal(size=(15,15))+1j*rng.normal(size=(15,15)))
S=rng.normal(size=(NS,k))+1j*rng.normal(size=(NS,k))
P4=list(itertools.permutations(range(4)))
def e2(v): s=v.sum(-1); return (s*s-(v*v).sum(-1))/2
def e3(v): s=v.sum(-1); p2=(v*v).sum(-1); p3=(v**3).sum(-1); return (s**3-3*s*p2+2*p3)/6
def res_c(X):
    B=np.hstack([np.eye(k),X])@Q   # k x 15
    Y=emb(S@B)  # NS,4,5
    out=[]
    for j in range(5):
        Z=np.delete(Y,j,axis=2)
        out.append(e2(Z).sum(-1)); out.append(e3(Z).sum(-1))
        pm=sum(Z[:,0,p[0]]*Z[:,1,p[1]]*Z[:,2,p[2]]*Z[:,3,p[3]] for p in P4); out.append(pm)
    return np.concatenate(out)
def res(x):
    X=(x[:k*(15-k)]+1j*x[k*(15-k):]).reshape(k,15-k); r=res_c(X); return np.concatenate([r.real,r.imag])
best=None
for trial in range(int(sys.argv[4]) if len(sys.argv)>4 else 3):
    x0=rng.normal(size=2*k*(15-k))*0.7
    sol=least_squares(res,x0,method='lm',max_nfev=4000,xtol=1e-15,ftol=1e-15,gtol=1e-15)
    X=(sol.x[:k*(15-k)]+1j*sol.x[k*(15-k):]).reshape(k,15-k)
    B=np.hstack([np.eye(k),X])@Q; sv=np.linalg.svd(B,compute_uv=False)
    # fresh check on orthonormalised basis
    U,_s,Vh=np.linalg.svd(B,full_matrices=False); Bo=Vh
    S2=rng.normal(size=(40,k))+1j*rng.normal(size=(40,k)); Y=emb(S2@Bo)
    fr=0
    for j in range(5):
        Z=np.delete(Y,j,axis=2); fr=max(fr,abs(e2(Z).sum(-1)).max(),abs(e3(Z).sum(-1)).max(),abs(sum(Z[:,0,p[0]]*Z[:,1,p[1]]*Z[:,2,p[2]]*Z[:,3,p[3]] for p in P4)).max())
    rs=np.linalg.norm(Y.sum(2),axis=1)
    print('k',k,'trial',trial,'cost %.2e'%sol.cost,'fresh %.1e'%fr,'sv %.2e..%.2e'%(sv.max(),sv.min()),flush=True)
    if fr<1e-9: np.save('sl_k%d_s%d_%d.npy'%(k,seed,trial),Bo)
