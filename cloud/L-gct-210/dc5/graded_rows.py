"""column-graded DC spaces with row vectors restricted to a row set R: K = sum_k A_k (x) chi_k, A_k ⊆ V_R."""
import sys, itertools, time
sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases'); sys.path.insert(0,'/home/claude/work/L-gct-210/dc5')
import numpy as np
from math import comb
from level import Pk
w=np.exp(2j*np.pi/5); CH=[w**(k*np.arange(5)) for k in range(5)]
def VR(R):
    M=np.array([np.eye(5)[i]-np.eye(5)[R[-1]] for i in R[:-1]]).T
    return np.linalg.qr(M)[0].T   # (|R|-1) x 5
def build(p,dims,Qs,Vb):
    m=len(Vb); mats=[]; pos=0
    for k,dk in enumerate(dims,start=1):
        if dk==0: continue
        X=p[pos:pos+dk*(m-dk)].reshape(dk,m-dk); pos+=dk*(m-dk)
        A=np.hstack([np.eye(dk),X])@Qs[k]@Vb
        for a in A: mats.append(np.outer(a,CH[k]))
    return np.array(mats)
def solve(dims,ks,starts,seed,Vb,tl=15,maxit=200):
    rng=np.random.default_rng(seed); m=len(Vb); d=sum(dims); npar=sum(dk*(m-dk) for dk in dims)
    nsamp=comb(d+max(ks)-1,max(ks))+15; t0=time.time(); best=(9,None)
    for s in range(starts):
        Qs={k:np.linalg.qr(rng.normal(size=(m,m))+1j*rng.normal(size=(m,m)))[0] for k in range(1,5)}
        p=0.7*(rng.normal(size=npar)+1j*rng.normal(size=npar))
        xs=rng.normal(size=(nsamp,d))+1j*rng.normal(size=(nsamp,d)); xs/=np.linalg.norm(xs,axis=1,keepdims=True)
        res=lambda q: Pk(np.einsum('ri,iab->rab',xs,build(q,dims,Qs,Vb)))[:,ks].reshape(-1)
        lam=1e-3; r=res(p); f=np.linalg.norm(r)
        for it in range(maxit):
            if npar==0: break
            h=1e-7; J=np.array([(res(p+h*np.eye(npar)[j])-r)/h for j in range(npar)]).T
            JH=J.conj().T; H=JH@J; g=JH@r
            st=np.linalg.solve(H+lam*np.diag(np.diag(H).real+1e-12),-g); pn=p+st; rn=res(pn); fn=np.linalg.norm(rn)
            if fn<f: p,r,f=pn,rn,fn; lam=max(lam/3,1e-12)
            else:
                lam*=4
                if lam>1e8: break
            if f<1e-12: break
        if f<best[0]: best=(f,build(p,dims,Qs,Vb))
        if f<1e-11 or time.time()-t0>tl: break
    return best
if __name__=='__main__':
    R=[int(c) for c in sys.argv[1]]; tot=int(sys.argv[2]); ks=[int(c) for c in sys.argv[3]]; Vb=VR(R); m=len(Vb)
    for dims in itertools.product(range(m+1),repeat=4):
        if sum(dims)!=tot: continue
        f,B=solve(list(dims),ks,int(sys.argv[4]),1,Vb,tl=float(sys.argv[5]))
        if f<1e-9: print(dims,'SOLVED res %.1e'%f,flush=True); np.save('gr_%s_%s.npy'%(sys.argv[1],''.join(map(str,dims))),B)
    print('done')
