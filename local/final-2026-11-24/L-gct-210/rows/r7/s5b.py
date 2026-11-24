# S_5: single strongly level 4x5 matrices with all five columns nonzero (Walsh coords, 15 unknowns); tangent dimension at LM hits
import numpy as np, itertools, sys
H=np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],dtype=complex)
P4=list(itertools.permutations(range(4)))
def perm(M): return sum(np.prod([M[i,p[i]] for i in range(4)]) for p in P4)
def C(Y):
    J=np.ones((4,5)); return np.array([perm((J+Y)[:,[c for c in range(5) if c!=j]])-24 for j in range(5)])
def mat(x): return H@x.reshape(5,3).T
SS=np.array([0.5,1.0,-0.7,1.3]); VMi=np.linalg.inv(np.array([[s**k for k in range(1,5)] for s in SS]))
def homog(Y): return (VMi@np.array([C(s*Y) for s in SS]))[1:].ravel()
def res(x,L): X=x.reshape(5,3); return np.concatenate([homog(mat(x)),[L[j]@X[j]-1 for j in range(5)]])
def jac(x,L,f0):
    Jm=np.zeros((len(f0),15),dtype=complex)
    for k in range(15):
        e=np.zeros(15,dtype=complex); e[k]=1e-7; Jm[:,k]=(res(x+e,L)-f0)/1e-7
    return Jm
rng=np.random.default_rng(int(sys.argv[1])); pts=[]
for trial in range(int(sys.argv[2])):
    x=rng.normal(size=15)+1j*rng.normal(size=15); L=rng.normal(size=(5,3))+1j*rng.normal(size=(5,3)); lam=1e-3
    f=res(x,L); nf=np.linalg.norm(f)
    for it in range(300):
        if nf<1e-13: break
        Jm=jac(x,L,f); dx=np.linalg.solve(Jm.conj().T@Jm+lam*np.eye(15),-Jm.conj().T@f); f2=res(x+dx,L)
        if np.linalg.norm(f2)<nf: x=x+dx; f=f2; nf=np.linalg.norm(f2); lam=max(lam/3,1e-12)
        else: lam*=4
    if nf<1e-10:
        Jm=jac(x,L,f)[:-5]; sv=np.linalg.svd(Jm,compute_uv=False); rk=int(np.sum(sv>1e-5*sv[0]))
        print('5col hit res %.1e tangent dim %d sv tail %s colnorms %s'%(nf,15-rk,np.array2string(sv[-6:],precision=2),np.round(np.linalg.norm(x.reshape(5,3),axis=1),3)),flush=True); pts.append(x)
    else: print('miss res %.1e'%nf,flush=True)
np.save('s5pts_%s.npy'%sys.argv[1],np.array(pts))
