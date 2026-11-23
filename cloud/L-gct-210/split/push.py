import sys,time; sys.path.insert(0,'.')
from core import *
from math import comb
from sviol import dcbasis, ROW, COL
from ext2 import fresh
from rab import info
DCB=dcbasis()
def setup(B,d=1):
    B=np.asarray(B); dim=len(B); k=dim-d
    # make delta first: replace basis by [D, complement]
    I=rde(B,1e-6); D=I['D'][:d]
    Lf=B.reshape(dim,-1); Df=D.reshape(d,-1); Qd,_=np.linalg.qr(Df.T)
    R=Lf-(Lf@Qd.conj())@Qd.T; u,s,vh=np.linalg.svd(R); comp=vh[:k]  # orthonormal complement rows
    Bn=np.concatenate([D,comp.reshape(k,5,5)+0j])
    # re-express comp as elements of span(B): project comp onto span(B)
    Qb,_=np.linalg.qr(Lf.T); compB=(comp@Qb.conj())@Qb.T
    Bn=np.concatenate([D,compB.reshape(k,5,5)])
    return Bn
def push(B,d,targets,tl=40,W=1.0,seed=0):
    rng=np.random.default_rng(seed); B=setup(B,d); dim=len(B); k=dim-d
    c,al,be,g=decomp(B)
    p=np.concatenate([g[m][:4,:4].reshape(-1) for m in range(d)]+[al[j][:4] for j in range(d,dim)]+[be[j][:4] for j in range(d,dim)]+[g[j][:4,:4].reshape(-1) for j in range(d,dim)])
    fixidx=[int(np.argmax(np.abs(p[16*m:16*m+16])))+16*m for m in range(d)]
    free=np.array([i for i in range(len(p)) if i not in fixidx])
    nsamp=comb(dim+4,5)+30; xs=rnd((nsamp,dim),rng); xs/=np.linalg.norm(xs,axis=1,keepdims=True)
    o=16*d
    def unpackP(p): return p[o:o+4*k].reshape(k,4).T   # 4 x k alpha coords
    def build(p):
        out=[np.einsum('m,mab->ab',p[16*m:16*m+16],DCB) for m in range(d)]
        for j in range(k):
            P=p[o+4*j:o+4*j+4]; M=p[o+4*k+4*j:o+4*k+4*j+4]; Y=p[o+8*k+16*j:o+8*k+16*j+16]
            out.append(np.einsum('p,pab->ab',P,ROW)+np.einsum('p,pab->ab',M,COL)+np.einsum('m,mab->ab',Y,DCB))
        return np.array(out)
    def smin(p):  # smallest singular value of alpha coordinate matrix (4 x k), as proxy use det of Gram
        A=unpackP(p); return np.linalg.svd(A,compute_uv=False)[-1]
    A0=unpackP(p); import itertools
    rows=max(itertools.combinations(range(4),k),key=lambda R: abs(np.linalg.det(A0[list(R)])))
    rows=list(rows)
    def gramdet(p):
        A=unpackP(p); return np.linalg.det(A[rows])
    npar=len(p); dB=np.zeros((npar,dim,5,5),complex)
    for m in range(d):
        for q in range(16): dB[16*m+q,m]=DCB[q]
    for j in range(k):
        for q in range(4): dB[o+4*j+q,d+j]=ROW[q]; dB[o+4*k+4*j+q,d+j]=COL[q]
        for q in range(16): dB[o+8*k+16*j+q,d+j]=DCB[q]
    dB=dB[free]
    def res(p,target,jac=True):
        T=np.einsum('ri,iab->rab',xs,build(p)); ex=W*(gramdet(p)-target)
        if not jac: return np.concatenate([Pk(T)[:,2:].reshape(-1),[ex]])
        P_,G=level.Pk_grad(T); dT=np.einsum('ri,qiab->rqab',xs,dB)
        J=np.einsum('rkab,rqab->rkq',G[:,2:],dT).reshape(-1,len(free))
        jr=np.zeros(len(free),complex); h=1e-7
        g0=gramdet(p)
        for qi,q in enumerate(free):
            if o<=q<o+4*k:
                pp=p.copy(); pp[q]+=h; jr[qi]=W*(gramdet(pp)-g0)/h
        return np.concatenate([P_[:,2:].reshape(-1),[ex]]), np.vstack([J,jr[None]])
    print(' start gramdet',gramdet(p),'smin',smin(p))
    for target in targets:
        lam=1e-3; r,J=res(p,target); f=np.linalg.norm(r); t0=time.time()
        while time.time()-t0<tl:
            H=J.conj().T@J; gr=J.conj().T@r
            pn=p.copy(); pn[free]+=np.linalg.solve(H+lam*np.diag(np.diag(H).real+1e-14),-gr)
            fn=np.linalg.norm(res(pn,target,False))
            if fn<f: p=pn; f=fn; lam=max(lam/3,1e-14); r,J=res(p,target)
            else:
                lam*=4
                if lam>1e10: break
            if f<1e-12: break
        Bn=build(p); lv=np.linalg.norm(r[:-1]) if True else 0
        print(' target %.2e: total res %.2e  gramdet %.2e  smin(alpha) %.3e  fresh %.2e'%(abs(target),f,abs(gramdet(p)),smin(p),fresh(Bn)),flush=True)
    return Bn
if __name__=='__main__':
    B=np.load(sys.argv[1]); d=int(sys.argv[2])
    g0=float(sys.argv[3]); facs=[float(x) for x in sys.argv[4].split(',')]
    Bn=push(B,d,[g0*f for f in facs],tl=float(sys.argv[5]))
    np.save('pushed.npy',Bn)
