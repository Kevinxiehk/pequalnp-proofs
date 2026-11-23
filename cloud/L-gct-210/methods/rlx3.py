# relaxation at fixed g in L: linear (U_g), quadric (4 Hessian coefficient forms), cubic (3 third-derivative coefficient forms)
import sys; sys.path.insert(0,"/home/claude/work/L-gct-210/methods")
import numpy as np, itertools, os
from scipy.optimize import least_squares
from rlx import setup, load_space
n=5; N=25; idx=[(i,j) for i in range(n) for j in range(n)]
def third(X):
    T=np.zeros((N,N,N),dtype=complex)
    for a,(i1,j1) in enumerate(idx):
        for b,(i2,j2) in enumerate(idx):
            if i2==i1 or j2==j1 or b<=a: continue
            for c,(i3,j3) in enumerate(idx):
                if c<=b or i3 in (i1,i2) or j3 in (j1,j2): continue
                R=[m for m in range(n) if m not in (i1,i2,i3)]; C=[m for m in range(n) if m not in (j1,j2,j3)]
                v=X[R[0],C[0]]*X[R[1],C[1]]+X[R[0],C[1]]*X[R[1],C[0]]
                for p in itertools.permutations((a,b,c)): T[p]=v
    return T
def coeffs3(g):
    ss=np.exp(2j*np.pi*np.arange(3)/3)*0.7
    vals=np.array([third(np.ones((n,n))+s*g) for s in ss]); V=np.vander(ss,3,increasing=True)
    return np.einsum('kj,j...->k...',np.linalg.inv(V),vals)
def search3(Fs,Ts,d,starts=4,nfev=300,seed=0,verbose=False,wc=1.0):
    rng=np.random.default_rng(seed); Np=Fs[0].shape[0]; iu=np.triu_indices(d)
    tri=[(a,b,c) for a in range(d) for b in range(a,d) for c in range(b,d)]; ta,tb,tc=map(np.array,zip(*tri))
    best=np.inf
    for st in range(starts):
        C=np.linalg.qr(rng.normal(size=(Np,Np))+1j*rng.normal(size=(Np,Np)))[0]
        Ys=[C.T@F@C for F in Fs]; Y3=[np.einsum('pqr,pa,qb,rc->abc',T,C,C,C) for T in Ts]
        def unpack(v): return (v[:d*(Np-d)]+1j*v[d*(Np-d):]).reshape(d,Np-d)
        def fun(v):
            E=np.hstack([np.eye(d),unpack(v)])
            r=[(E@Y@E.T)[iu] for Y in Ys]+[wc*np.einsum('pqr,ap,bq,cr->abc',T,E,E,E)[ta,tb,tc] for T in Y3]
            r=np.concatenate(r); return np.concatenate([r.real,r.imag])
        def jac(v):
            E=np.hstack([np.eye(d),unpack(v)]); blocks=[]
            for Y in Ys:
                YE=Y@E.T; J=np.zeros((d,d,d,Np-d),dtype=complex)
                for i in range(d): J[i,:,i,:]+=YE[d:,:].T; J[:,i,i,:]+=YE[d:,:].T
                blocks.append(J[iu[0],iu[1]].reshape(len(iu[0]),-1))
            for T in Y3:
                Mt=np.einsum('mpq,bp,cq->mbc',T[d:],E,E)    # (Np-d) x d x d
                J=np.zeros((d,d,d,d,Np-d),dtype=complex)  # dR_abc/dX_ij
                for i in range(d):
                    J[i,:,:,i,:]+=np.transpose(Mt,(1,2,0)); J[:,i,:,i,:]+=np.transpose(Mt,(1,2,0)); J[:,:,i,i,:]+=np.transpose(Mt,(1,2,0))
                blocks.append(wc*J[ta,tb,tc].reshape(len(tri),-1))
            Jc=np.vstack(blocks); return np.block([[Jc.real,-Jc.imag],[Jc.imag,Jc.real]])
        v0=rng.normal(size=2*d*(Np-d))*0.5
        m=len(Ys)*len(iu[0])+len(Y3)*len(tri); meth='lm' if m>=d*(Np-d) else 'trf'
        sol=least_squares(fun,v0,jac=jac,method=meth,max_nfev=nfev,xtol=1e-15,ftol=1e-15,gtol=1e-15)
        r=np.linalg.norm(sol.fun); best=min(best,r)
        if verbose: print('   start',st,'res %.2e'%r,flush=True)
        if best<1e-10: break
    return best
if __name__=='__main__':
    f=sys.argv[1]; seed=int(sys.argv[2]); ds=[int(a) for a in sys.argv[3:]]
    V=load_space(f); rng=np.random.default_rng(seed); c=rng.normal(size=V.shape[0])+1j*rng.normal(size=V.shape[0]); g=(c@V).reshape(n,n); g/=np.linalg.norm(g)
    Q,Fs,rk=setup(g); Ts=[np.einsum('pqr,pa,qb,rc->abc',T,Q,Q,Q) for T in coeffs3(g)]
    # sanity: does a known space containing g satisfy the cubic forms?
    if len(sys.argv)>0 and os.environ.get('KNOWN'):
        K=load_space(os.environ['KNOWN']); A=np.hstack([Q,g.ravel()[:,None]]); sol=np.linalg.lstsq(A,K.T,rcond=None)[0]
        Lq=sol[:-1].T; Lq=np.linalg.svd(Lq)[2][:np.linalg.matrix_rank(Lq,1e-8)]
        print('known space: fit',np.linalg.norm(A@sol-K.T),'quad iso',['%.0e'%np.abs(Lq@F@Lq.T).max() for F in Fs],'cubic',['%.0e'%np.abs(np.einsum('pqr,ap,bq,cr->abc',T,Lq,Lq,Lq)).max() for T in Ts])
    print('gradrank',rk,'quot',Q.shape[1],'cubic ranks(flattened)',[np.linalg.matrix_rank(T.reshape(T.shape[0],-1),1e-8) for T in Ts],flush=True)
    for d in ds: print('  d=%d (level %d) quad+cubic best %.2e'%(d,d+1,search3(Fs,Ts,d,starts=int(os.environ.get('ST','3')),verbose=True)),flush=True)
