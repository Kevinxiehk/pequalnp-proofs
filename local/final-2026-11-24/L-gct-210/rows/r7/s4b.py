import numpy as np, sys
sys.argv=[sys.argv[0]]+sys.argv[1:]
exec(open('s4num.py').read().split("rng=np.random")[0])
def res4(x,L):   # four column normalisations l_j . x_j = 1
    Y=mat(x); X=x.reshape(4,3); r=list(homog(Y)); r+= [L[j]@X[j]-1 for j in range(4)]; return np.array(r)
def jac4(x,L,h=1e-7):
    f0=res4(x,L); Jm=np.zeros((len(f0),12),dtype=complex)
    for k in range(12):
        e=np.zeros(12,dtype=complex); e[k]=h; Jm[:,k]=(res4(x+e,L)-f0)/h
    return Jm
def lm4(x,L,it=300):
    lam=1e-3
    for _ in range(it):
        f=res4(x,L); nf=np.linalg.norm(f)
        if nf<1e-13: break
        Jm=jac4(x,L); A=Jm.conj().T@Jm; g=Jm.conj().T@f
        dx=np.linalg.solve(A+lam*np.eye(12),-g)
        if np.linalg.norm(res4(x+dx,L))<nf: x=x+dx; lam=max(lam/3,1e-12)
        else: lam*=4
    return x,np.linalg.norm(res4(x,L))
rng=np.random.default_rng(int(sys.argv[1])); pts=[]
for trial in range(int(sys.argv[2])):
    x=rng.normal(size=12)+1j*rng.normal(size=12); L=rng.normal(size=(4,3))+1j*rng.normal(size=(4,3))
    x,r=lm4(x,L)
    if r<1e-10:
        Jm=jac4(x,L)[:-4]; sv=np.linalg.svd(Jm,compute_uv=False); rk=int(np.sum(sv>1e-7*sv[0]))
        X=x.reshape(4,3); sig=X.sum(0); G=X@X.T
        print('4col hit res %.1e tangent dim %d  sv tail %s  diagG %s sig.sig %s'%(r,12-rk,np.array2string(sv[-5:],precision=2),np.round(np.diag(G),3),np.round(sig@sig,3)),flush=True)
        pts.append(x)
np.save('s4pts4_%s.npy'%sys.argv[1],np.array(pts))
