# extend a fixed strongly level 4x5 space F by k vectors (Grassmannian chart in the orthogonal complement), LM
import numpy as np, itertools, sys
from scipy.optimize import least_squares
name=sys.argv[1]; k=int(sys.argv[2]); seed=int(sys.argv[3]); ntr=int(sys.argv[4]); rng=np.random.default_rng(seed); NS=60
I=1j; chi=lambda a: np.array([I**(a*j) for j in range(4)]); w=np.exp(2j*np.pi/3)
def E(v,j):
    t=np.zeros((4,5),complex); t[:,j]=v; return t.ravel()
if name=='I': F=[E(chi(1),0),E(chi(1),1),E(chi(1),2)]
elif name=='I2': F=[E(chi(1),0)-E(chi(1),1),E(chi(1),1)-E(chi(1),2)]
elif name=='II':
    z=np.array([1,w,w*w,0]); F=[E(z,0)-E(z,1),E(z.conj(),2)-E(z.conj(),3)]
F=np.array(F); f=len(F)
# column-centred ambient basis (15) as rows
amb=[]
for j in range(5):
    for b in ([1,-1,0,0],[0,1,-1,0],[0,0,1,-1]): amb.append(E(np.array(b,complex),j))
amb=np.array(amb)
# orthogonal complement of F inside ambient (hermitian)
Qa=np.linalg.qr(amb.T)[0]  # 20x15
Fc=Qa.conj().T@F.T  # 15 x f coords
U,s,Vh=np.linalg.svd(Fc,full_matrices=True); comp=U[:,f:]  # 15 x (15-f)
Cb=(Qa@comp).T  # (15-f) x 20 complement basis
D=15-f; Q,_=np.linalg.qr(rng.normal(size=(D,D))+1j*rng.normal(size=(D,D)))
S=rng.normal(size=(NS,f+k))+1j*rng.normal(size=(NS,f+k)); P4=list(itertools.permutations(range(4)))
def e2(v): s=v.sum(-1); return (s*s-(v*v).sum(-1))/2
def e3(v): s=v.sum(-1); p2=(v*v).sum(-1); p3=(v**3).sum(-1); return (s**3-3*s*p2+2*p3)/6
m=k*(D-k)
def basis(x):
    X=(x[:m]+1j*x[m:]).reshape(k,D-k); return np.vstack([F,np.hstack([np.eye(k),X])@Q@Cb])
def res(x):
    Y=(S@basis(x)).reshape(-1,4,5); out=[]
    for j in range(5):
        Z=np.delete(Y,j,axis=2); out+=[e2(Z).sum(-1),e3(Z).sum(-1),sum(Z[:,0,p[0]]*Z[:,1,p[1]]*Z[:,2,p[2]]*Z[:,3,p[3]] for p in P4)]
    r=np.concatenate(out); return np.concatenate([r.real,r.imag])
r0=res(np.zeros(2*m)) if False else None
for tr in range(ntr):
    sol=least_squares(res,rng.normal(size=2*m)*0.7,method='lm',max_nfev=3000,xtol=1e-15,ftol=1e-15,gtol=1e-15)
    B=basis(sol.x); T=B[f:].reshape(k,4,5); srow=T.sum(2)
    print(name,'+',k,'tr',tr,'cost %.1e'%sol.cost,'rowsum rank of new part',int(np.linalg.matrix_rank(srow,1e-6)),flush=True)
