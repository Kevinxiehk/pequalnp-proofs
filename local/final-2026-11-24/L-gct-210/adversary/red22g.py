import numpy as np, sys
exec(open('/home/kevxhk/work/L-gct-210/adversary/red22lm2.py').read().split('def search')[0])
def search(d,useG,starts,seed=0):
    rng=np.random.default_rng(seed); m=7
    for s in range(starts):
        Q,_=np.linalg.qr(rng.normal(size=(m,m))+1j*rng.normal(size=(m,m))); Q=Q.T
        X=0.3*(rng.normal(size=(d,m-d))+1j*rng.normal(size=(d,m-d)))
        xs=rng.normal(size=(80,d))+1j*rng.normal(size=(80,d))
        Bof=lambda X: np.hstack([np.eye(d),X])@Q
        def res(X):
            E3,GX=parts((xs@Bof(X)).T); return np.concatenate([E3,GX]) if useG else E3
        lam=1e-3
        for it in range(300):
            r=res(X); f=np.linalg.norm(r)
            J=np.zeros((len(r),X.size),complex); h=1e-7
            for k in range(X.size):
                Xp=X.copy().reshape(-1); Xp[k]+=h; J[:,k]=(res(Xp.reshape(X.shape))-r)/h
            H=J.conj().T@J; g=J.conj().T@r
            Xn=X+np.linalg.solve(H+lam*np.diag(np.diag(H).real+1e-12),-g).reshape(X.shape); fn=np.linalg.norm(res(Xn))
            if fn<f: X=Xn; lam=max(lam/3,1e-12)
            else: lam*=4
            if fn<1e-12 or lam>1e8: break
        B=Bof(X); f=np.linalg.norm(res(X))
        print(f" d={d} useG={useG} s{s}: res {f:.2e} |X| {np.linalg.norm(X):.1f} c-sv {np.round(np.linalg.svd(B[:,5:],compute_uv=False),3)}",flush=True)
search(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4]))
