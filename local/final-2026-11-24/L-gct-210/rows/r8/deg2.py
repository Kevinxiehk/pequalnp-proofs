# degree-2 part of a 3-column K: B_a + B_b + B_c = 1 with B_j in O(3,C). Do solutions with all rank(A_j) >= 2 exist? (A_j = (1-B_j)/2)
import numpy as np, sys
rng=np.random.default_rng(int(sys.argv[1]))
I=np.eye(3)
def res(x):
    Ba=x[:9].reshape(3,3); Bb=x[9:].reshape(3,3); Bc=I-Ba-Bb
    return np.concatenate([(M.T@M-I)[np.triu_indices(3)] for M in (Ba,Bb,Bc)])
def jac(x,f):
    J=np.zeros((len(f),18),complex)
    for k in range(18):
        e=np.zeros(18,complex); e[k]=1e-7; J[:,k]=(res(x+e)-f)/1e-7
    return J
for st in range(int(sys.argv[2])):
    x=rng.normal(size=18)+1j*rng.normal(size=18); lam=1e-3; f=res(x); nf=np.linalg.norm(f)
    for it in range(300):
        if nf<1e-13: break
        J=jac(x,f); dx=np.linalg.lstsq(J.conj().T@J+lam*np.eye(18),-J.conj().T@f,rcond=None)[0]; f2=res(x+dx)
        if np.linalg.norm(f2)<nf: x=x+dx; f=f2; nf=np.linalg.norm(f2); lam=max(lam/3,1e-14)
        else: lam*=4
    Ba=x[:9].reshape(3,3); Bb=x[9:].reshape(3,3); Bc=I-Ba-Bb
    sv=[np.linalg.svd((I-M)/2,compute_uv=False) for M in (Ba,Bb,Bc)]
    rk=[int(np.sum(s>1e-6*max(1,s[0]))) for s in sv]
    J=jac(x,f); svJ=np.linalg.svd(J,compute_uv=False); tdim=18-int(np.sum(svJ>1e-6*svJ[0]))
    print('res %.1e ranks %s  det B %s  tangent dim %d'%(nf,rk,np.round([np.linalg.det(M) for M in (Ba,Bb,Bc)],3),tdim),flush=True)
