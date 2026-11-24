import numpy as np, sys
seed,nst,pat=int(sys.argv[1]),int(sys.argv[2]),sys.argv[3]; rng=np.random.default_rng(seed); I=np.eye(3)
def res(x):
    B=[x[9*k:9*k+9].reshape(3,3) for k in range(4)]; B.append(3*I-sum(B))
    r=[(M.T@M-I)[np.triu_indices(3)] for M in B]; r.append(np.array([np.linalg.det(M)-(1 if p=='+' else -1) for M,p in zip(B,pat)]))
    return np.concatenate(r)
ok=0
for st in range(nst):
    x=rng.normal(size=36)+1j*rng.normal(size=36); lam=1e-3; f=res(x); nf=np.linalg.norm(f)
    for it in range(300):
        if nf<1e-13: break
        J=np.zeros((len(f),36),complex)
        for k in range(36):
            e=np.zeros(36,complex); e[k]=1e-7; J[:,k]=(res(x+e)-f)/1e-7
        dx=np.linalg.lstsq(J.conj().T@J+lam*np.eye(36),-J.conj().T@f,rcond=None)[0]; f2=res(x+dx)
        if np.linalg.norm(f2)<nf: x=x+dx; f=f2; nf=np.linalg.norm(f2); lam=max(lam/3,1e-14)
        else: lam*=4
    B=[x[9*k:9*k+9].reshape(3,3) for k in range(4)]; B.append(3*I-sum(B))
    rk=sorted(int(np.sum(np.linalg.svd((I-M)/2,compute_uv=False)>1e-4)) for M in B)
    ok+=nf<1e-10; print(pat,'res %.1e ranks %s'%(nf,rk),flush=True)
print(pat,'converged',ok,'of',nst)
