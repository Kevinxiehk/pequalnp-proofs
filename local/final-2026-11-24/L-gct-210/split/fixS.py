import sys,time; sys.path.insert(0,'.')
from seed13 import *
from math import comb
from rab import info
from ext2 import fresh
seed=int(sys.argv[1]); rng=np.random.default_rng(seed)
L=np.load(sys.argv[2]); Lf=L.reshape(len(L),-1); Q,_=np.linalg.qr(Lf.T); O=Q.T.reshape(len(L),5,5)
D=rde(L,1e-6)['D'][0]
c=rnd((2,len(L)),rng); S=np.concatenate([D[None],np.einsum('qk,kij->qij',c,O)])
E=ext_space(S); C=complement(S,E); m=len(C)
cS,alS,beS,gS=decomp(S); Pa,_=np.linalg.qr(alS[1:].T)
cC,alC,beC,gC=decomp(C.reshape(m,5,5))
# functional ell(x) = component of alpha(C^T x) orthogonal to alpha(S), along a fixed direction n
Aout=alC-(alC@Pa.conj())@Pa.T     # m x 5 : alpha parts with alpha(S) projected out
u,s,vh=np.linalg.svd(Aout); print('rank of alpha-out map on complement:',int((s>1e-8).sum()),'sv',s.round(4))
n=vh[0].conj(); ell=Aout@n        # ell(x) = sum x_q <alpha_out(C_q), n>
xs=rnd((comb(4+4,5)+20,4),rng); xs/=np.linalg.norm(xs,axis=1,keepdims=True)
def run(start):
    r2=np.random.default_rng(start)
    # constraint ell.x = 1 ; parametrise x = x_p + N z
    xp=ell.conj()/np.vdot(ell,ell); u,s,vh=np.linalg.svd(ell[None]); N=vh[1:].T
    z=r2.normal(size=m-1)+1j*r2.normal(size=m-1)
    def res(z,jac=True):
        x=xp+N@z; y=(C.T@x).reshape(5,5); B=np.concatenate([S,y[None]]); T=np.einsum('ri,iab->rab',xs,B)
        sc=1/max(1,np.linalg.norm(x))**5
        if not jac: return Pk(T)[:,1:].reshape(-1)*sc
        P,G=level.Pk_grad(T); dy=(C.T@N).T.reshape(-1,5,5)
        J=np.einsum('rkab,pab->rkp',G[:,1:],dy)*xs[:,3][:,None,None]
        return P[:,1:].reshape(-1)*sc, J.reshape(-1,m-1)*sc
    lam=1e-3; r,J=res(z); f=np.linalg.norm(r); t0=time.time()
    while time.time()-t0<12:
        H=J.conj().T@J; g=J.conj().T@r
        zn=z+np.linalg.solve(H+lam*np.diag(np.diag(H).real+1e-14),-g); fn=np.linalg.norm(res(zn,False))
        if fn<f: z=zn; f=fn; lam=max(lam/3,1e-14); r,J=res(z)
        else:
            lam*=4
            if lam>1e10: break
        if f<1e-13: break
    x=xp+N@z; y=(C.T@x).reshape(5,5); return f,np.concatenate([S,y[None]])
out=[]
t0=time.time()
for st in range(40):
    f,B4=run(st); out.append(f)
    if f<1e-11:
        I=info(B4,1e-6); Lf4=B4.reshape(4,-1); Q4,_=np.linalg.qr(Lf4.T); O4=Q4.T.reshape(4,5,5); cc,al,be,g=decomp(O4)
        print(' start %d res %.2e fresh %.1e'%(st,f,fresh(B4)),I,'sv a',np.linalg.svd(al,compute_uv=False).round(4),'sv b',np.linalg.svd(be,compute_uv=False).round(4),flush=True)
        np.save('fixS_%d_%d.npy'%(seed,st),B4)
    if time.time()-t0>float(sys.argv[3]): break
print('min res',min(out))
