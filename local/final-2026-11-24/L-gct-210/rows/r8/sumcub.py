# degree 2 + the SUMMED cubic only: sum_j c(B_j s) = (NC-2) c(s) for all s (c = x1 x2 x3, Walsh), NC active columns, columns kept active.
import numpy as np, sys
seed,nst,NC=map(int,sys.argv[1:4]); rng=np.random.default_rng(seed); I=np.eye(3)
S=rng.normal(size=(16,3))+1j*rng.normal(size=(16,3)); Ls=rng.normal(size=(NC,9))+1j*rng.normal(size=(NC,9))
def cub(x): return x[0]*x[1]*x[2]
def res(v):
    B=[v[9*k:9*k+9].reshape(3,3) for k in range(NC-1)]; B.append((NC-2)*I-sum(B)); z=v[9*(NC-1):]
    r=[(M.T@M-I)[np.triu_indices(3)] for M in B]
    r.append(np.array([sum(cub(M@s) for M in B)-(NC-2)*cub(s) for s in S]))
    r.append(np.array([z[j]*(Ls[j]@((I-B[j])/2).ravel())-1 for j in range(NC)]))
    return np.concatenate(r)
nv=9*(NC-1)+NC; hits=0
for st in range(nst):
    v=rng.normal(size=nv)+1j*rng.normal(size=nv); lam=1e-3; f=res(v); nf=np.linalg.norm(f)
    for it in range(250):
        if nf<1e-12: break
        J=np.zeros((len(f),nv),complex)
        for k in range(nv):
            e=np.zeros(nv,complex); e[k]=1e-7; J[:,k]=(res(v+e)-f)/1e-7
        dx=np.linalg.lstsq(J.conj().T@J+lam*np.eye(nv),-J.conj().T@f,rcond=None)[0]; f2=res(v+dx)
        if np.linalg.norm(f2)<nf: v=v+dx; f=f2; nf=np.linalg.norm(f2); lam=max(lam/3,1e-14)
        else: lam*=4
    hits+=nf<1e-10; print('NC=%d start %d res %.2e'%(NC,st,nf),flush=True)
print('NC=%d HITS %d of %d'%(NC,hits,nst))
