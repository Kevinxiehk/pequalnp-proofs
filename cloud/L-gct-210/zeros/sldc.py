# sanity for Lemma FR(c): DC strongly level 4x5 spaces N: dim 2 should exist, dim 3 should not
import numpy as np, itertools, sys
from scipy.optimize import least_squares
k=int(sys.argv[1]); seed=int(sys.argv[2]); ntr=int(sys.argv[3]); rng=np.random.default_rng(seed); NS=50
dc=[]
for i in range(3):
    for j in range(4):
        t=np.zeros((4,5)); t[i,j]=1; t[i,4]-=1; t[3,j]-=1; t[3,4]+=1; dc.append(t.ravel())
dc=np.linalg.qr(np.array(dc).T)[0].T
Q,_=np.linalg.qr(rng.normal(size=(12,12))+1j*rng.normal(size=(12,12)))
S=rng.normal(size=(NS,k))+1j*rng.normal(size=(NS,k)); P4=list(itertools.permutations(range(4)))
def e2(v): s=v.sum(-1); return (s*s-(v*v).sum(-1))/2
def e3(v): s=v.sum(-1); p2=(v*v).sum(-1); p3=(v**3).sum(-1); return (s**3-3*s*p2+2*p3)/6
def rc(B):
    Y=(S@B).reshape(-1,4,5); out=[]
    for j in range(5):
        Z=np.delete(Y,j,axis=2); out+=[e2(Z).sum(-1),e3(Z).sum(-1),sum(Z[:,0,p[0]]*Z[:,1,p[1]]*Z[:,2,p[2]]*Z[:,3,p[3]] for p in P4)]
    return np.concatenate(out)
m=k*(12-k)
def res(x):
    X=(x[:m]+1j*x[m:]).reshape(k,12-k); r=rc(np.hstack([np.eye(k),X])@Q@dc); return np.concatenate([r.real,r.imag])
for tr in range(ntr):
    sol=least_squares(res,rng.normal(size=2*m)*0.6,method='lm',max_nfev=4000,xtol=1e-15,ftol=1e-15,gtol=1e-15)
    X=(sol.x[:m]+1j*sol.x[m:]).reshape(k,12-k); B=np.hstack([np.eye(k),X])@Q@dc
    T=B.reshape(k,4,5); cr=[np.linalg.matrix_rank(T[:,:,j],1e-6) for j in range(5)]
    rown=[float(np.round(np.linalg.norm(T[:,i,:]),6)) for i in range(4)]
    print('DC k',k,'tr',tr,'cost %.1e'%sol.cost,'col ranks',[int(c) for c in cr],'row norms',rown,flush=True)
