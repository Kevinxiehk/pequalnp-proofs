# lines in S_4 through a sampled 4-column point h: unknown direction h' (12 complex), all mixed (s,t)-coefficients of the
# homogeneous parts of C(s h + t h') must vanish; normalisation l1.h' = 1, l2.h' = 0 (kills h' -> h' + c h)
import numpy as np, sys, itertools
exec(open('s4num.py').read().split("rng=np.random")[0])
ST=[(1.0,0.3),(0.4,1.0),(1.0,-0.8),(-0.6,1.0),(1.0,1.7),(0.9,-0.2),(1.0,0.0)]
def mixed(h,hp):
    # values of homogeneous parts (deg 2,3,4) of C at s*h+t*hp for several (s,t); subtract pure-h part; return all
    Yh=mat(h); Yp=mat(hp); r=[]
    for (s,t) in ST[:6]:
        co=homog(s*Yh+t*Yp).reshape(3,5); co0=homog(s*Yh).reshape(3,5); r.append((co-co0).ravel())
    return np.concatenate(r)
def resl(hp,h,l1,l2): return np.concatenate([mixed(h,hp),[l1@hp-1,l2@hp]])
def lml(hp,h,l1,l2,it=150):
    lam=1e-3
    f=resl(hp,h,l1,l2); nf=np.linalg.norm(f)
    for _ in range(it):
        if nf<1e-12: break
        Jm=np.zeros((len(f),12),dtype=complex)
        for k in range(12):
            e=np.zeros(12,dtype=complex); e[k]=1e-7; Jm[:,k]=(resl(hp+e,h,l1,l2)-f)/1e-7
        A=Jm.conj().T@Jm; g=Jm.conj().T@f
        dx=np.linalg.solve(A+lam*np.eye(12),-g); f2=resl(hp+dx,h,l1,l2)
        if np.linalg.norm(f2)<nf: hp=hp+dx; f=f2; nf=np.linalg.norm(f); lam=max(lam/3,1e-12)
        else: lam*=4
    return hp,nf
pts=np.load(sys.argv[1]); rng=np.random.default_rng(int(sys.argv[2])); nst=int(sys.argv[3])
for ip,h in enumerate(pts):
    best=1e9
    for st in range(nst):
        l1=rng.normal(size=12)+1j*rng.normal(size=12); l2=rng.normal(size=12)+1j*rng.normal(size=12)
        hp,nf=lml(rng.normal(size=12)+1j*rng.normal(size=12),h,l1,l2)
        best=min(best,nf)
        if nf<1e-9:
            s1=h.reshape(4,3).sum(0); s2=hp.reshape(4,3).sum(0)
            rk=np.linalg.svd(np.array([s1,s2]),compute_uv=False)
            print('point %d start %d: LINE FOUND res %.1e  row-sum sing.vals %s'%(ip,st,nf,np.round(rk,6)),flush=True)
    print('point %d: best residual %.2e over %d starts'%(ip,best,nst),flush=True)
