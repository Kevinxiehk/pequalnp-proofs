import numpy as np, sys
# coords v = (Z11,Z12,Z21,s1,s2,c1,c2), Z22 = -(Z11+Z12+Z21+s1+s2+c1+c2)
def E3(v):
    Z11,Z12,Z21,s1,s2,c1,c2=v; Z22=-(Z11+Z12+Z21+s1+s2+c1+c2)
    R1=Z11+Z12;R2=Z21+Z22;K1=Z11+Z21;K2=Z12+Z22
    F=(s1+s2)*(c1+c2)+s1*R2+s2*R1+Z11*Z22+Z12*Z21+c1*K2+c2*K1
    return c1*(s1*Z22+s2*Z12)+c2*(s1*Z21+s2*Z11)-(c1+c2)*F
def Qmu(v,mu):  # case c2=mu c1 : quadratic A1+mu A2-(1+mu)F, with c2 = mu*c1
    pass
def search(d,starts=20,seed=0):
    rng=np.random.default_rng(seed); best=9
    for s in range(starts):
        B=rng.normal(size=(d,7))+1j*rng.normal(size=(d,7))
        xs=rng.normal(size=(60,d))+1j*rng.normal(size=(60,d))
        def res(B): V=(xs@B).T; return E3(V)
        lam=1e-3
        for it in range(300):
            r=res(B); f=np.linalg.norm(r)
            J=np.zeros((len(r),B.size),complex); h=1e-7
            for k in range(B.size):
                Bp=B.copy().reshape(-1); Bp[k]+=h; J[:,k]=(res(Bp.reshape(B.shape))-r)/h
            H=J.conj().T@J; g=J.conj().T@r
            st=np.linalg.solve(H+lam*np.diag(np.diag(H).real+1e-12),-g)
            Bn=B+st.reshape(B.shape); fn=np.linalg.norm(res(Bn))
            if fn<f: B=Bn; lam=max(lam/3,1e-12)
            else: lam*=4
            if f<1e-11 or lam>1e8: break
            B=B/np.linalg.norm(B,axis=1,keepdims=True)
        f=np.linalg.norm(res(B)); best=min(best,f)
        sv=np.linalg.svd(B[:,5:],compute_uv=False)
        print(f' d={d} start {s}: res {f:.2e}  c-rank sv {np.round(sv,3)}',flush=True)
    return best
d=int(sys.argv[1]); search(d,int(sys.argv[2]))
