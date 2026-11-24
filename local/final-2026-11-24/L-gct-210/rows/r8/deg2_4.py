# degree-2 data on exactly 4 active columns: B_0..B_3 in O(3,C), sum = 2; optionally a prescribed sign pattern (det B_j = eps_j)
import numpy as np, sys
seed,nst=int(sys.argv[1]),int(sys.argv[2]); pat=sys.argv[3] if len(sys.argv)>3 else None
rng=np.random.default_rng(seed); I=np.eye(3)
def res(x):
    B=[x[9*k:9*k+9].reshape(3,3) for k in range(3)]; B.append(2*I-sum(B))
    r=[(M.T@M-I)[np.triu_indices(3)] for M in B]
    if pat: r.append(np.array([np.linalg.det(M)-(1 if s=='+' else -1) for M,s in zip(B,pat)]))
    return np.concatenate(r)
cnt={}
for st in range(nst):
    x=rng.normal(size=27)+1j*rng.normal(size=27); lam=1e-3; f=res(x); nf=np.linalg.norm(f)
    for it in range(300):
        if nf<1e-13: break
        J=np.zeros((len(f),27),complex)
        for k in range(27):
            e=np.zeros(27,complex); e[k]=1e-7; J[:,k]=(res(x+e)-f)/1e-7
        dx=np.linalg.lstsq(J.conj().T@J+lam*np.eye(27),-J.conj().T@f,rcond=None)[0]; f2=res(x+dx)
        if np.linalg.norm(f2)<nf: x=x+dx; f=f2; nf=np.linalg.norm(f2); lam=max(lam/3,1e-14)
        else: lam*=4
    B=[x[9*k:9*k+9].reshape(3,3) for k in range(3)]; B.append(2*I-sum(B))
    rk=tuple(int(np.sum(np.linalg.svd((I-M)/2,compute_uv=False)>1e-6)) for M in B)
    sg=''.join('+' if np.real(np.linalg.det(M))>0 else '-' for M in B)
    key=(nf<1e-10, ''.join(sorted(sg,reverse=True)), tuple(sorted(rk)))
    cnt[key]=cnt.get(key,0)+1
for k,v in sorted(cnt.items(),key=lambda z:-z[1]): print(v,'converged' if k[0] else 'NOT converged','signs',k[1],'ranks',k[2])
