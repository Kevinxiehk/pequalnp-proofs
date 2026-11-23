# structured LM for strongly level 4x5 L' with q = dim s(L') in {1,2}, dN = dim DC part; S isotropic/degenerate or generic
import numpy as np, itertools, sys
from scipy.optimize import least_squares
q=int(sys.argv[1]); dN=int(sys.argv[2]); iso=int(sys.argv[3]); seed=int(sys.argv[4]); ntr=int(sys.argv[5])
rng=np.random.default_rng(seed); NS=60
f=np.linalg.qr(np.array([[1,-1,0,0],[0,1,-1,0],[0,0,1,-1]],float).T)[0]
dc=[]
for i in range(3):
    for j in range(4):
        t=np.zeros((4,5)); t[i,j]=1; t[i,4]-=1; t[3,j]-=1; t[3,4]+=1; dc.append(t.ravel())
dc=np.linalg.qr(np.array(dc).T)[0].T
Qn,_=np.linalg.qr(rng.normal(size=(12,12))+1j*rng.normal(size=(12,12)))
k=q+dN; S=rng.normal(size=(NS,k))+1j*rng.normal(size=(NS,k))
P4=list(itertools.permutations(range(4)))
def e2(v): s=v.sum(-1); return (s*s-(v*v).sum(-1))/2
def e3(v): s=v.sum(-1); p2=(v*v).sum(-1); p3=(v**3).sum(-1); return (s**3-3*s*p2+2*p3)/6
npar=2+12*q+dN*(12-dN)
def build(z):
    t=z[0]; t2=z[1]; off=2
    u=(1-t*t)*f[:,0]+1j*(1+t*t)*f[:,1]+2*t*f[:,2]
    if iso: sig=[u]
    else: sig=[f[:,0]+t*f[:,1]+t2*f[:,2]]
    if q==2:
        if iso: w=f[:,2]; sig.append(f[:,0]-(f[:,0]@u)/(w@u)*w)
        else: sig.append(f[:,2]+t2*f[:,1])
    rows=[]
    for a in range(q):
        Y=np.zeros((4,5),complex); Y[:,0]=sig[a]; rows.append(Y.ravel()+z[off:off+12]@dc); off+=12
    C=z[off:off+dN*(12-dN)].reshape(dN,12-dN)
    Nb=np.hstack([np.eye(dN),C])@Qn@dc
    return np.vstack(rows+[Nb])
def resz(z):
    B=build(z); Y=(S@B).reshape(-1,4,5); out=[]
    for j in range(5):
        Z=np.delete(Y,j,axis=2); out+= [e2(Z).sum(-1), e3(Z).sum(-1), sum(Z[:,0,p[0]]*Z[:,1,p[1]]*Z[:,2,p[2]]*Z[:,3,p[3]] for p in P4)]
    return np.concatenate(out)
def res(x):
    z=x[:npar]+1j*x[npar:]; r=resz(z); return np.concatenate([r.real,r.imag])
for tr in range(ntr):
    x0=rng.normal(size=2*npar)*0.6
    sol=least_squares(res,x0,method='lm',max_nfev=6000,xtol=1e-15,ftol=1e-15,gtol=1e-15)
    z=sol.x[:npar]+1j*sol.x[npar:]; B=build(z); sv=np.linalg.svd(B,compute_uv=False)
    print('q',q,'dN',dN,'iso',iso,'seed',seed,'tr',tr,'cost %.2e'%sol.cost,'sv',np.round(sv,3),flush=True)
    if sol.cost<1e-18: np.save('sqd_%d%d%d_%d_%d.npy'%(q,dN,iso,seed,tr),B)
