import sys,time; sys.path.insert(0,'.')
from core import *
from math import comb
from sviol import dcbasis, ROW, COL
DCB=dcbasis()
def run(d,k,starts=8,seed=0,tlimit=60,maxit=300,WDET=1.0,verbose=False):
    """search level space D (+) S, D DC dim d (chart), S dim k with alpha=P f, beta=M f both rank k (det of top minors = 1)"""
    rng=np.random.default_rng(seed); t0=time.time(); dim=d+k; nsamp=comb(dim+4,5)+10; best=(np.inf,None)
    for s in range(starts):
        Qd,_=np.linalg.qr(rnd((16,16),rng)); Qd=Qd.T  # random basis of DC coords
        nZ=d*(16-d); npar=nZ+16*k+8*k
        p=0.4*rnd(npar,rng)
        Pm0=np.eye(4)[:,:k]; p[nZ+16*k:nZ+16*k+4*k]=(Pm0+0.3*rnd((4,k),rng)).reshape(-1); p[nZ+20*k:]=(Pm0+0.3*rnd((4,k),rng)).reshape(-1)
        xs=rnd((nsamp,dim),rng); xs/=np.linalg.norm(xs,axis=1,keepdims=True)
        DCq=np.einsum('pq,qab->pab',Qd,DCB)
        def unpack(p):
            Z=p[:nZ].reshape(d,16-d); Y=p[nZ:nZ+16*k].reshape(k,16); P=p[nZ+16*k:nZ+20*k].reshape(4,k); M=p[nZ+20*k:].reshape(4,k); return Z,Y,P,M
        def build(p):
            Z,Y,P,M=unpack(p); B=[]
            for m in range(d): B.append(DCq[m]+np.einsum('q,qab->ab',Z[m],DCq[d:]))
            for j in range(k): B.append(np.einsum('p,pab->ab',P[:,j],ROW)+np.einsum('p,pab->ab',M[:,j],COL)+np.einsum('m,mab->ab',Y[j],DCB))
            return np.array(B)
        dB=np.zeros((npar,dim,5,5),complex)
        for m in range(d):
            for q in range(16-d): dB[m*(16-d)+q,m]=DCq[d+q]
        for j in range(k):
            for m in range(16): dB[nZ+16*j+m,d+j]=DCB[m]
            for pp in range(4): dB[nZ+16*k+pp*k+j,d+j]=ROW[pp]; dB[nZ+20*k+pp*k+j,d+j]=COL[pp]
        def extra(p,jac):
            Z,Y,P,M=unpack(p); e=[]; Js=[]
            for off,X in ((nZ+16*k,P),(nZ+20*k,M)):
                S=X[:k,:k]; dt=np.linalg.det(S); e.append(WDET*(dt-1))
                if jac:
                    jr=np.zeros(npar,complex); cof=dt*np.linalg.inv(S).T
                    for a in range(k):
                        for b in range(k): jr[off+a*k+b]=WDET*cof[a,b]
                    Js.append(jr)
            return np.array(e),(np.array(Js) if jac else None)
        def res(p,jac=True):
            B=build(p); T=np.einsum('ri,iab->rab',xs,B); ex,Je=extra(p,jac)
            if not jac: return np.concatenate([Pk(T)[:,2:].reshape(-1),ex])
            P_,G=level.Pk_grad(T); dT=np.einsum('ri,qiab->rqab',xs,dB)
            J=np.einsum('rkab,rqab->rkq',G[:,2:],dT).reshape(-1,npar)
            return np.concatenate([P_[:,2:].reshape(-1),ex]), np.vstack([J,Je])
        lam=1e-3; r,J=res(p); f=np.linalg.norm(r)
        for it in range(maxit):
            if time.time()-t0>tlimit: break
            H=J.conj().T@J; g=J.conj().T@r
            pn=p+np.linalg.solve(H+lam*np.diag(np.diag(H).real+1e-12),-g)
            fn=np.linalg.norm(res(pn,False))
            if fn<f: p=pn; lam=max(lam/3,1e-12); r,J=res(p); f=fn
            else:
                lam*=4
                if lam>1e8: break
            if f<1e-12: break
        Z,Y,P,M=unpack(p)
        if verbose: print(f'  (d,k)=({d},{k}) start {s}: res {f:.2e} svP {np.linalg.svd(P,compute_uv=False).round(3)} svM {np.linalg.svd(M,compute_uv=False).round(3)}',flush=True)
        if f<best[0]: best=(f,build(p))
        if f<1e-11 or time.time()-t0>tlimit: break
    return best
if __name__=='__main__':
    d,k=int(sys.argv[1]),int(sys.argv[2])
    f,B=run(d,k,starts=int(sys.argv[3]),seed=int(sys.argv[4]),tlimit=float(sys.argv[5]),verbose=True)
    from ext2 import fresh
    print(f'RESULT (d,k)=({d},{k}) best res {f:.2e} fresh {fresh(B):.2e}')
    np.save(f'sgen_{d}_{k}.npy',B)
