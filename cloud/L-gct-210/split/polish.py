import sys,time; sys.path.insert(0,'.')
from core import *
from math import comb
from sviol import dcbasis, ROW, COL
from ext2 import fresh
from rab import info
DCB=dcbasis()
def polish(B,d,maxit=600,tlimit=150,seed=0):
    rng=np.random.default_rng(seed); B=np.asarray(B); dim=len(B); k=dim-d
    c,al,be,g=decomp(B)
    X0=[g[m][:4,:4].reshape(-1) for m in range(d)]
    p=np.concatenate([np.concatenate(X0)]+[al[j][:4] for j in range(d,dim)]+[be[j][:4] for j in range(d,dim)]+[g[j][:4,:4].reshape(-1) for j in range(d,dim)])
    # parameters: delta coords (16 d), P (4k), M (4k), Y (16k); fix normalisation: keep delta_m coordinate m0 fixed
    fixidx=[np.argmax(np.abs(X0[m]))+16*m for m in range(d)]
    free=np.array([i for i in range(len(p)) if i not in fixidx])
    nsamp=comb(dim+4,5)+30; xs=rnd((nsamp,dim),rng); xs/=np.linalg.norm(xs,axis=1,keepdims=True)
    def build(p):
        out=[np.einsum('m,mab->ab',p[16*m:16*m+16],DCB) for m in range(d)]
        o=16*d
        for j in range(k):
            P=p[o+4*j:o+4*j+4]; M=p[o+4*k+4*j:o+4*k+4*j+4]; Y=p[o+8*k+16*j:o+8*k+16*j+16]
            out.append(np.einsum('p,pab->ab',P,ROW)+np.einsum('p,pab->ab',M,COL)+np.einsum('m,mab->ab',Y,DCB))
        return np.array(out)
    npar=len(p); dB=np.zeros((npar,dim,5,5),complex)
    for m in range(d):
        for q in range(16): dB[16*m+q,m]=DCB[q]
    o=16*d
    for j in range(k):
        for q in range(4): dB[o+4*j+q,d+j]=ROW[q]; dB[o+4*k+4*j+q,d+j]=COL[q]
        for q in range(16): dB[o+8*k+16*j+q,d+j]=DCB[q]
    dB=dB[free]
    def res(p,jac=True):
        T=np.einsum('ri,iab->rab',xs,build(p))
        if not jac: return Pk(T)[:,2:].reshape(-1)
        P_,G=level.Pk_grad(T); dT=np.einsum('ri,qiab->rqab',xs,dB)
        return P_[:,2:].reshape(-1), np.einsum('rkab,rqab->rkq',G[:,2:],dT).reshape(-1,len(free))
    lam=1e-3; r,J=res(p); f=np.linalg.norm(r); t0=time.time()
    for it in range(maxit):
        if time.time()-t0>tlimit: break
        H=J.conj().T@J; gr=J.conj().T@r
        step=np.linalg.solve(H+lam*np.diag(np.diag(H).real+1e-12),-gr)
        pn=p.copy(); pn[free]+=step
        fn=np.linalg.norm(res(pn,False))
        if fn<f: p=pn; lam=max(lam/3,1e-14); r,J=res(p); f=fn
        else:
            lam*=4
            if lam>1e10: break
        if f<1e-13: break
    Bn=build(p); return f,Bn
if __name__=='__main__':
    B=np.load(sys.argv[1]); d=int(sys.argv[2])
    f,Bn=polish(B,d,tlimit=float(sys.argv[3]))
    print('polished res %.2e fresh %.2e'%(f,fresh(Bn)), info(Bn,1e-6))
    Lf=Bn.reshape(len(Bn),-1); Q,_=np.linalg.qr(Lf.T); O=Q.T.reshape(len(Bn),5,5); c,al,be,g=decomp(O)
    print('sv al',np.linalg.svd(al,compute_uv=False).round(5),'sv be',np.linalg.svd(be,compute_uv=False).round(5))
    np.save(sys.argv[1].replace('.npy','_pol.npy'),Bn)
