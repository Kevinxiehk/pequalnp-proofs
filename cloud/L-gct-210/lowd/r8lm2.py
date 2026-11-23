# r=8 test with bidegree components: (k,j) = coeff of s^j in P_k(s x + y), x in X_A, y in X_B.
import sys, time
sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases'); sys.path.insert(0,'/home/claude/work/L-gct-210/lowd')
import numpy as np, level
from d1lm import DCB, ROW, COL, rnd
def run(comps,starts,seed,tlimit,maxit=300,nx=60):
    rng=np.random.default_rng(seed); t0=time.time(); outl=[]
    for s in range(starts):
        npar=128; p=0.5*rnd(npar,rng)
        xa=rnd((nx,4),rng); xb=rnd((nx,4),rng)
        L=6; ss=np.exp(2j*np.pi*np.arange(L)/L)
        co=np.zeros((nx,L,8),complex); co[:,:,:4]=ss[None,:,None]*xa[:,None,:]; co[:,:,4:]=xb[:,None,:]
        co=co.reshape(-1,8)
        Finv=np.exp(-2j*np.pi*np.outer(np.arange(L),np.arange(L))/L)/L
        def build(p):
            Y=p.reshape(8,16); B=[]
            for k in range(4): B.append(ROW[k]+np.einsum('m,mab->ab',Y[k],DCB))
            for k in range(4): B.append(COL[k]+np.einsum('m,mab->ab',Y[4+k],DCB))
            return np.array(B)
        dB=np.zeros((npar,8,5,5),complex)
        for k in range(8):
            for m in range(16): dB[16*k+m,k]=DCB[m]
        def res(p,jac=True):
            B=build(p); T=np.einsum('ri,iab->rab',co,B)
            if jac: P,G=level.Pk_grad(T)
            else: P=level.Pk(T)
            C=np.einsum('jl,rlk->rjk',Finv,P.reshape(nx,L,-1))
            r=np.concatenate([C[:,j,k] for k,j in comps])
            if not jac: return r
            dT=np.einsum('ri,qiab->rqab',co,dB)
            Jf=np.einsum('rkab,rqab->rkq',G,dT).reshape(nx,L,G.shape[1],npar)
            JC=np.einsum('jl,rlkq->rjkq',Finv,Jf)
            return r,np.concatenate([JC[:,j,k,:] for k,j in comps],axis=0)
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
        print(f'comps={comps} start {s}: res {f:.2e} it {it}',flush=True)
        outl.append((f,build(p)))
        if time.time()-t0>tlimit: break
    return outl
if __name__=='__main__':
    comps=[tuple(int(c) for c in w) for w in sys.argv[1].split(',')]
    out=run(comps,int(sys.argv[2]),int(sys.argv[3]),float(sys.argv[4]))
    f,B=min(out,key=lambda t:t[0]); np.save(f'/home/claude/work/L-gct-210/lowd/r8c_{sys.argv[1].replace(",","_")}.npy',B)
