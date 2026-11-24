import sys, time
sys.path.insert(0,'/home/kevxhk/work/L-gct-086/smallcases')
import numpy as np, level
from math import comb
n=5
def dcbasis():
    out=[]
    for i in range(4):
        for j in range(4):
            M=np.zeros((5,5)); M[i,j]=1; M[i,4]=-1; M[4,j]=-1; M[4,4]=1; out.append(M)
    return np.array(out,dtype=complex)
DCB=dcbasis()
F=np.zeros((4,5))
for p in range(4): F[p,p]=1; F[p,4]=-1
ROW=np.array([np.outer(F[p],np.ones(5)) for p in range(4)],dtype=complex)
COL=np.array([np.outer(np.ones(5),F[p]) for p in range(4)],dtype=complex)
def rnd(shape,rng): return rng.normal(size=shape)+1j*rng.normal(size=shape)
def run(ks,starts,seed,tlimit,maxit=300):
    rng=np.random.default_rng(seed); t0=time.time(); d=5
    outl=[]
    for s in range(starts):
        x0=rnd(16,rng); x0/=np.linalg.norm(x0)
        Qz,_=np.linalg.qr(np.column_stack([x0.conj(),rnd((16,15),rng)])); Zb=Qz[:,1:].T
        npar=15+64+16
        p=0.5*rnd(npar,rng); p[79:]=rnd(16,rng)
        nsamp=comb(d+max(ks)-1,max(ks))+10
        xs=rnd((nsamp,d),rng); xs/=np.linalg.norm(xs,axis=1,keepdims=True)
        def build(p):
            z=p[:15]@Zb; Y=p[15:79].reshape(4,16); M=p[79:].reshape(4,4)
            B=[np.einsum('m,mab->ab',x0+z,DCB)]
            for k in range(4):
                B.append(ROW[k]+np.einsum('p,pab->ab',M[:,k],COL)+np.einsum('m,mab->ab',Y[k],DCB))
            return np.array(B)
        dB=np.zeros((npar,5,5,5),complex)
        for q in range(15): dB[q,0]=np.einsum('m,mab->ab',Zb[q],DCB)
        for k in range(4):
            for m in range(16): dB[15+16*k+m,k+1]=DCB[m]
        for pp in range(4):
            for k in range(4): dB[79+4*pp+k,k+1]=COL[pp]
        kk=[k for k in ks]
        def res(p,jac=True):
            B=build(p); T=np.einsum('ri,iab->rab',xs,B)
            if not jac: return level.Pk(T)[:,kk].reshape(-1)
            P,G=level.Pk_grad(T)
            dT=np.einsum('ri,qiab->rqab',xs,dB)
            J=np.einsum('rkab,rqab->rkq',G[:,kk],dT)
            return P[:,kk].reshape(-1), J.reshape(-1,npar)
        lam=1e-3; r,J=res(p); f=np.linalg.norm(r)
        for it in range(maxit):
            if time.time()-t0>tlimit: break
            H=J.conj().T@J; gg=J.conj().T@r
            pn=p+np.linalg.solve(H+lam*np.diag(np.diag(H).real+1e-12),-gg)
            fn=np.linalg.norm(res(pn,False))
            if fn<f: p=pn; lam=max(lam/3,1e-12); r,J=res(p); f=fn
            else:
                lam*=4
                if lam>1e8: break
            if f<1e-12: break
        M=p[79:].reshape(4,4); sv=np.linalg.svd(M,compute_uv=False)
        print(f'ks={ks} start {s}: res {f:.2e} it {it} svM {sv.round(3)}',flush=True)
        outl.append((f,build(p)))
        if time.time()-t0>tlimit: break
    return outl
if __name__=='__main__':
    ks=[int(c) for c in sys.argv[1]]
    out=run(ks,int(sys.argv[2]),int(sys.argv[3]),float(sys.argv[4]))
    f,B=min(out,key=lambda t:t[0]); np.save(f'/home/kevxhk/work/L-gct-210/lowd/d1_{sys.argv[1]}.npy',B)
