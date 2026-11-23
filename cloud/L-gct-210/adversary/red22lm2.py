import numpy as np, sys
def parts(v):
    Z11,Z12,Z21,s1,s2,c1,c2=v; Z22=-(Z11+Z12+Z21+s1+s2+c1+c2)
    R1=Z11+Z12;R2=Z21+Z22;K1=Z11+Z21;K2=Z12+Z22
    F=(s1+s2)*(c1+c2)+s1*R2+s2*R1+Z11*Z22+Z12*Z21+c1*K2+c2*K1
    E3=c1*(s1*Z22+s2*Z12)+c2*(s1*Z21+s2*Z11)-(c1+c2)*F
    GX=(2/3)*s1*s2+F
    return E3,GX
def search(d,useG,starts,seed=0):
    rng=np.random.default_rng(seed)
    for s in range(starts):
        B=rng.normal(size=(d,7))+1j*rng.normal(size=(d,7))
        xs=rng.normal(size=(60,d))+1j*rng.normal(size=(60,d))
        def res(B):
            E3,GX=parts((xs@B).T); return np.concatenate([E3,GX]) if useG else E3
        lam=1e-3
        for it in range(300):
            r=res(B); f=np.linalg.norm(r)
            J=np.zeros((len(r),B.size),complex); h=1e-7
            for k in range(B.size):
                Bp=B.copy().reshape(-1); Bp[k]+=h; J[:,k]=(res(Bp.reshape(B.shape))-r)/h
            H=J.conj().T@J; g=J.conj().T@r
            Bn=B+np.linalg.solve(H+lam*np.diag(np.diag(H).real+1e-12),-g).reshape(B.shape); fn=np.linalg.norm(res(Bn))
            if fn<f: B=Bn; lam=max(lam/3,1e-12)
            else: lam*=4
            if f<1e-11 or lam>1e8: break
            B=B/np.linalg.norm(B,axis=1,keepdims=True)
        f=np.linalg.norm(res(B)); sv=np.linalg.svd(B[:,5:],compute_uv=False)
        # rank of GX on I
        E3,GX=parts((xs@B).T)
        print(f" d={d} useG={useG} start {s}: res {f:.2e} c-sv {np.round(sv,3)} B-sv {np.round(np.linalg.svd(B,compute_uv=False),4)}",flush=True)
search(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]))
