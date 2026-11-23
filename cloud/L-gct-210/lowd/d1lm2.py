# LM for L = Cg + graph(alpha -> (alpha, M alpha, Gamma alpha)), imposing only selected
# components (k,j): coefficient of lam^j in P_k(lam g + x), x in span(x1..x4).
import sys, time
sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases')
sys.path.insert(0,'/home/claude/work/L-gct-210/lowd')
import numpy as np, level
from d1lm import DCB, ROW, COL, rnd
MSCALE=1.0
def run(comps,starts,seed,tlimit,maxit=300,nx=40,verbose=True):
    rng=np.random.default_rng(seed); t0=time.time(); outl=[]
    ks=sorted(set(k for k,j in comps))
    for s in range(starts):
        x0=rnd(16,rng); x0/=np.linalg.norm(x0)
        Qz,_=np.linalg.qr(np.column_stack([x0.conj(),rnd((16,15),rng)])); Zb=Qz[:,1:].T
        npar=15+64+16
        p=0.5*rnd(npar,rng); p[79:]=MSCALE*rnd(16,rng)
        xs=rnd((nx,4),rng); xs/=np.linalg.norm(xs,axis=1,keepdims=True)
        L=6; lams=np.exp(2j*np.pi*np.arange(L)/L)
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
        # coefficient vectors: point (r,l) = lam_l * B0 + sum xs[r] B[1:]
        co=np.zeros((nx,L,5),complex); co[:,:,0]=lams[None,:]; co[:,:,1:]=xs[:,None,:]
        co=co.reshape(-1,5)
        Finv=np.exp(-2j*np.pi*np.outer(np.arange(L),np.arange(L))/L)/L  # coef_j = sum_l Finv[j,l] val_l
        def res(p,jac=True):
            B=build(p); T=np.einsum('ri,iab->rab',co,B)
            if jac: P,G=level.Pk_grad(T)
            else: P=level.Pk(T)
            P=P.reshape(nx,L,-1)
            C=np.einsum('jl,rlk->rjk',Finv,P)  # C[r,j,k]
            r=np.concatenate([C[:,j,k] for k,j in comps])
            if not jac: return r
            dT=np.einsum('ri,qiab->rqab',co,dB)
            Jfull=np.einsum('rkab,rqab->rkq',G,dT).reshape(nx,L,G.shape[1],npar)
            JC=np.einsum('jl,rlkq->rjkq',Finv,Jfull)
            J=np.concatenate([JC[:,j,k,:] for k,j in comps],axis=0)
            return r,J
        lam=1e-3; r,J=res(p); f=np.linalg.norm(r)
        for it in range(maxit):
            if time.time()-t0>tlimit: break
            H=J.conj().T@J; gg=J.conj().T@r
            pn=p+np.linalg.solve(H+lam*np.diag(np.diag(H).real+1e-6)+1e-14*np.eye(len(p)),-gg)
            fn=np.linalg.norm(res(pn,False))
            if fn<f: p=pn; lam=max(lam/3,1e-12); r,J=res(p); f=fn
            else:
                lam*=4
                if lam>1e8: break
            if f<1e-12: break
        M=p[79:].reshape(4,4); sv=np.linalg.svd(M,compute_uv=False)
        if verbose: print(f'comps={comps} start {s}: res {f:.2e} it {it} svM {sv.round(3)}',flush=True)
        outl.append((f,build(p),sv))
        if time.time()-t0>tlimit: break
    return outl
if __name__=='__main__':
    comps=[tuple(int(c) for c in w) for w in sys.argv[1].split(',')]
    out=run(comps,int(sys.argv[2]),int(sys.argv[3]),float(sys.argv[4]))
    f,B,sv=min(out,key=lambda t:t[0]); np.save(f'/home/claude/work/L-gct-210/lowd/d1c_{sys.argv[1].replace(",","_")}.npy',B)
