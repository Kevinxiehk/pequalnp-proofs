"""Column-graded DC spaces K = sum_k A_k (x) chi_k, A_k subset V (sum-zero C^5), chi_k = (w^{kj})_j.
LM over Grassmannian charts of the A_k.  usage: graded.py dims(e.g. 1111) ks starts seed"""
import sys, itertools, time
sys.path.insert(0,'/home/kevxhk/work/L-gct-086/smallcases')
import numpy as np
from math import comb
from level import Pk
w=np.exp(2j*np.pi/5)
CH=[w**(k*np.arange(5)) for k in range(5)]
Vb=np.linalg.qr(np.vstack([np.eye(5)[i]-np.eye(5)[4] for i in range(4)]).T)[0].T  # orthonormal real basis of V (4x5)
def build(params, dims, Qs):
    mats=[]; pos=0
    for k,dk in enumerate(dims, start=1):
        if dk==0: continue
        X=params[pos:pos+dk*(4-dk)].reshape(dk,4-dk); pos+=dk*(4-dk)
        A=np.hstack([np.eye(dk),X])@Qs[k]@Vb       # dk x 5 rows a
        for a in A: mats.append(np.outer(a,CH[k]))
    return np.array(mats)
def resid(params,dims,Qs,xs,ks):
    B=build(params,dims,Qs); T=np.einsum('ri,iab->rab',xs,B)
    return Pk(T)[:,ks].reshape(-1)
def solve(dims,ks,starts,seed,tl=60,maxit=200):
    rng=np.random.default_rng(seed); d=sum(dims); npar=sum(dk*(4-dk) for dk in dims)
    nsamp=comb(d+max(ks)-1,max(ks))+15; t0=time.time(); sols=[]
    for s in range(starts):
        Qs={}
        for k in range(1,5):
            Z=rng.normal(size=(4,4))+1j*rng.normal(size=(4,4)); Qs[k]=np.linalg.qr(Z)[0]
        p=0.7*(rng.normal(size=npar)+1j*rng.normal(size=npar))
        xs=rng.normal(size=(nsamp,d))+1j*rng.normal(size=(nsamp,d)); xs/=np.linalg.norm(xs,axis=1,keepdims=True)
        lam=1e-3; r=resid(p,dims,Qs,xs,ks); f=np.linalg.norm(r)
        for it in range(maxit):
            if npar==0: break
            h=1e-7; J=np.array([(resid(p+h*np.eye(npar)[j],dims,Qs,xs,ks)-r)/h for j in range(npar)]).T
            JH=J.conj().T; H=JH@J; g=JH@r
            st=np.linalg.solve(H+lam*np.diag(np.diag(H).real+1e-12),-g)
            pn=p+st; rn=resid(pn,dims,Qs,xs,ks); fn=np.linalg.norm(rn)
            if fn<f: p,r,f=pn,rn,fn; lam=max(lam/3,1e-12)
            else:
                lam*=4
                if lam>1e8: break
            if f<1e-12: break
        sols.append((f,p.copy(),Qs))
        if time.time()-t0>tl: break
    return sols
if __name__=='__main__':
    dims=[int(c) for c in sys.argv[1]]; ks=[int(c) for c in sys.argv[2]]
    sols=solve(dims,ks,int(sys.argv[3]),int(sys.argv[4]))
    fs=sorted(s[0] for s in sols); print(sys.argv[1],'best res',['%.1e'%f for f in fs[:5]], 'n_solved',sum(f<1e-9 for f in fs),'/',len(fs))
