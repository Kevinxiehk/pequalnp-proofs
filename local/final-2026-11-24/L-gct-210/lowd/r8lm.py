# LM: does an 8-dim space X_A + X_B (alpha-part onto V with beta=0, beta-part onto V with alpha=0)
# with P_k = 0 (k in ks) exist?  (r = 8 case).  Optional DC g (withg=1) -> dim 9.
import sys, time
sys.path.insert(0,'/home/kevxhk/work/L-gct-086/smallcases'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/lowd')
import numpy as np, level
from d1lm import DCB, ROW, COL, rnd
from math import comb
def run(ks,withg,starts,seed,tlimit,maxit=300):
    rng=np.random.default_rng(seed); t0=time.time(); outl=[]
    for s in range(starts):
        x0=rnd(16,rng); x0/=np.linalg.norm(x0)
        Qz,_=np.linalg.qr(np.column_stack([x0.conj(),rnd((16,15),rng)])); Zb=Qz[:,1:].T
        ng=15 if withg else 0; npar=ng+128; d=8+(1 if withg else 0)
        p=0.5*rnd(npar,rng)
        nsamp=comb(d+max(ks)-1,max(ks))+20
        xs=rnd((nsamp,d),rng); xs/=np.linalg.norm(xs,axis=1,keepdims=True)
        def build(p):
            Y=p[ng:].reshape(8,16); B=[]
            if withg: B.append(np.einsum('m,mab->ab',x0+p[:15]@Zb,DCB))
            for k in range(4): B.append(ROW[k]+np.einsum('m,mab->ab',Y[k],DCB))
            for k in range(4): B.append(COL[k]+np.einsum('m,mab->ab',Y[4+k],DCB))
            return np.array(B)
        dB=np.zeros((npar,d,5,5),complex)
        for q in range(ng): dB[q,0]=np.einsum('m,mab->ab',Zb[q],DCB)
        o=1 if withg else 0
        for k in range(8):
            for m in range(16): dB[ng+16*k+m,o+k]=DCB[m]
        def res(p,jac=True):
            B=build(p); T=np.einsum('ri,iab->rab',xs,B)
            if not jac: return level.Pk(T)[:,ks].reshape(-1)
            P,G=level.Pk_grad(T)
            dT=np.einsum('ri,qiab->rqab',xs,dB)
            J=np.einsum('rkab,rqab->rkq',G[:,ks],dT)
            return P[:,ks].reshape(-1), J.reshape(-1,npar)
        lam=1e-3; r,J=res(p); f=np.linalg.norm(r)
        for it in range(maxit):
            if time.time()-t0>tlimit: break
            H=J.conj().T@J; gg=J.conj().T@r
            pn=p+np.linalg.solve(H+lam*np.diag(np.diag(H).real+1e-6)+1e-14*np.eye(npar),-gg)
            fn=np.linalg.norm(res(pn,False))
            if fn<f: p=pn; lam=max(lam/3,1e-12); r,J=res(p); f=fn
            else:
                lam*=4
                if lam>1e8: break
            if f<1e-12: break
        print(f'ks={ks} withg={withg} start {s}: res {f:.2e} it {it}',flush=True)
        outl.append((f,build(p)))
        if time.time()-t0>tlimit: break
    return outl
if __name__=='__main__':
    ks=[int(c) for c in sys.argv[1]]; wg=int(sys.argv[2])
    out=run(ks,wg,int(sys.argv[3]),int(sys.argv[4]),float(sys.argv[5]))
    f,B=min(out,key=lambda t:t[0]); np.save(f'/home/kevxhk/work/L-gct-210/lowd/r8_{sys.argv[1]}_{wg}.npy',B)
