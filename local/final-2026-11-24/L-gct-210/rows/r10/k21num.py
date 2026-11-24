# strongly level 3-spaces with a doubly centred element: K = span(h1, h2, n), n doubly centred; all in Walsh coordinates (column-centred).
# residuals: homogeneous parts (deg 2,3,4) of the deletion vector at random points of K vanish; n has zero row sums; normalisations.
import numpy as np, itertools, sys
H=np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],dtype=complex)
P4=list(itertools.permutations(range(4)))
def perm(M): return sum(np.prod([M[i,p[i]] for i in range(4)]) for p in P4)
def C(Y):
    J=np.ones((4,5)); return np.array([perm((J+Y)[:,[c for c in range(5) if c!=j]])-24 for j in range(5)])
SS=np.array([0.5,1.0,-0.7,1.3]); VMi=np.linalg.inv(np.array([[s**k for k in range(1,5)] for s in SS]))
def homog(Y): return (VMi@np.array([C(s*Y) for s in SS]))[1:].ravel()
def mat(x): return H@x.reshape(5,3).T
seed,nst=int(sys.argv[1]),int(sys.argv[2]); rng=np.random.default_rng(seed)
W=rng.normal(size=(8,3))+1j*rng.normal(size=(8,3)); L=rng.normal(size=(3,15))+1j*rng.normal(size=(3,15))
def res(v):
    x=v.reshape(3,15); Ms=[mat(xx) for xx in x]; r=[]
    for w in W: r.extend(homog(w[0]*Ms[0]+w[1]*Ms[1]+w[2]*Ms[2]))
    r.extend(Ms[2].sum(1))                       # n doubly centred: zero row sums
    r.extend([L[k]@x[k]-1 for k in range(3)])
    return np.array(r)
for st in range(nst):
    v=rng.normal(size=45)+1j*rng.normal(size=45); lam=1e-3; f=res(v); nf=np.linalg.norm(f)
    for it in range(200):
        if nf<1e-12: break
        J=np.zeros((len(f),45),complex)
        for k in range(45):
            e=np.zeros(45,complex); e[k]=1e-7; J[:,k]=(res(v+e)-f)/1e-7
        dx=np.linalg.lstsq(J.conj().T@J+lam*np.eye(45),-J.conj().T@f,rcond=None)[0]; f2=res(v+dx)
        if np.linalg.norm(f2)<nf: v=v+dx; f=f2; nf=np.linalg.norm(f2); lam=max(lam/3,1e-14)
        else: lam*=4
    x=v.reshape(3,15); Ms=[mat(xx) for xx in x]
    S=np.array([M.sum(1) for M in Ms]); q=int(np.sum(np.linalg.svd(S,compute_uv=False)>1e-6))
    cols=[int(np.sum(np.linalg.svd(np.array([M[:,j] for M in Ms]),compute_uv=False)>1e-6)) for j in range(5)]
    Kb=np.array([M.ravel() for M in Ms]); d3=int(np.sum(np.linalg.svd(Kb,compute_uv=False)>1e-6))
    print('start %d res %.1e  dim %d  row-sum rank q=%d  column ranks %s'%(st,nf,d3,q,cols),flush=True)
    if nf<1e-10 and q==2 and d3==3: np.save('k21_s%d_%d.npy'%(seed,st),np.array(Ms))
