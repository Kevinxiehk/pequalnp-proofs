import sys,time; sys.path.insert(0,'.')
from core import *
from math import comb
# DC basis (16)
def dcbasis():
    out=[]
    for i in range(4):
        for j in range(4):
            M=np.zeros((5,5)); M[i,j]=1; M[i,4]=-1; M[4,j]=-1; M[4,4]=1; out.append(M)
    return np.array(out,dtype=complex)
DCB=dcbasis()
F=np.zeros((4,5)); 
for p in range(4): F[p,p]=1; F[p,4]=-1
ROW=np.array([np.outer(F[p],np.ones(5)) for p in range(4)],dtype=complex)  # alpha=f_p -> matrix f_p 1^T
COL=np.array([np.outer(np.ones(5),F[p]) for p in range(4)],dtype=complex)  # beta=f_p
def build(x0,z,Y,M,mode):
    x=x0+z
    B=[np.einsum('m,mab->ab',x,DCB)]
    for k in range(4):
        if mode=='graph': a=ROW[k]+np.einsum('p,pab->ab',M[:,k],COL)
        else: a=COL[k]   # calibration: R = B
        B.append(a+np.einsum('m,mab->ab',Y[k],DCB))
    return np.array(B)
def run(mode,starts=10,seed=0,tlimit=150,maxit=200):
    rng=np.random.default_rng(seed); t0=time.time(); d=5; nsamp=comb(d+4,5)+10; out=[]
    for s in range(starts):
        x0=rnd(16,rng); x0/=np.linalg.norm(x0)
        Qz,_=np.linalg.qr(np.column_stack([x0.conj(),rnd((16,15),rng)])); Zb=Qz[:,1:].T  # 15 x 16 basis of complement (hermitian)
        npar=15+64+(16 if mode=='graph' else 0)
        p=0.5*rnd(npar,rng)
        xs=rnd((nsamp,d),rng); xs/=np.linalg.norm(xs,axis=1,keepdims=True)
        def unpack(p):
            z=p[:15]@Zb; Y=p[15:79].reshape(4,16); M=p[79:].reshape(4,4) if mode=='graph' else None
            return z,Y,M
        # derivative tensors dB/dp : list of (basis index, matrix) per param
        dB=np.zeros((npar,5,5,5),complex)
        for q in range(15): dB[q,0]=np.einsum('m,mab->ab',Zb[q],DCB)
        for k in range(4):
            for m in range(16): dB[15+16*k+m,k+1]=DCB[m]
        if mode=='graph':
            for pp in range(4):
                for k in range(4): dB[79+4*pp+k,k+1]=COL[pp]
        def res(p,jac=True):
            z,Y,M=unpack(p); B=build(x0,z,Y,M,mode); T=np.einsum('ri,iab->rab',xs,B)
            if not jac: return Pk(T)[:,2:].reshape(-1)
            P,G=level.Pk_grad(T)
            dT=np.einsum('ri,qiab->rqab',xs,dB)
            J=np.einsum('rkab,rqab->rkq',G[:,2:],dT)
            return P[:,2:].reshape(-1), J.reshape(-1,npar)
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
        z,Y,M=unpack(p); B=build(x0,z,Y,M,mode)
        print(f' {mode} start {s}: res {f:.2e}  |p|max {np.abs(p).max():.1f}',flush=True); out.append((f,B))
        if time.time()-t0>tlimit: break
    return out
if __name__=='__main__':
    mode=sys.argv[1]; out=run(mode,starts=int(sys.argv[2]),seed=int(sys.argv[3]),tlimit=float(sys.argv[4]))
    f,B=min(out,key=lambda t:t[0]); np.save(f'sviol_{mode}.npy',B)
