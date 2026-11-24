# numerical: (4,1) spaces L' = K + C Z over the two-column (2,1) kernels K = span{u(e0+e1)^T, (p+e)e0^T+(p-e)e1^T, d(e0-e1)^T}
# unknowns: u, d (isotropic, Walsh, normalised by a random functional), p, e (Walsh), Z (4x5), m (5, sum 0, random normalisation)
import numpy as np, itertools, sys
H=np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],dtype=complex)
P4=list(itertools.permutations(range(4)))
def perm(M): return sum(np.prod([M[i,p[i]] for i in range(4)]) for p in P4)
def C(Y):
    J=np.ones((4,5)); return np.array([perm((J+Y)[:,[c for c in range(5) if c!=j]])-24 for j in range(5)])
seed,nst=int(sys.argv[1]),int(sys.argv[2]); rng=np.random.default_rng(seed)
Wpts=rng.normal(size=(10,4))+1j*rng.normal(size=(10,4)); lu=rng.normal(size=3)+1j*rng.normal(size=3); ld=rng.normal(size=3)+1j*rng.normal(size=3); lm=rng.normal(size=5)+1j*rng.normal(size=5)
def unpack(x): return x[0:3],x[3:6],x[6:9],x[9:12],x[12:32].reshape(4,5),x[32:37]
def res(x):
    u,d,p,e,Z,m=unpack(x); r=[u@u, d@d, u@p, d@e, p@p-1, e@e-1, lu@u-1, ld@d-1, m.sum(), lm@m-1]
    r+=list(Z.sum(0)-m)
    u4,d4,p4,e4=H@u,H@d,H@p,H@e
    K=[np.outer(u4,[1,1,0,0,0]), np.outer(p4+e4,[1,0,0,0,0])+np.outer(p4-e4,[0,1,0,0,0]), np.outer(d4,[1,-1,0,0,0]), Z]
    for w in Wpts:
        Y=sum(wi*Ki for wi,Ki in zip(w,K)); cv=C(Y); r+=list(cv-cv.sum()/5-(cv@np.conj(m))/(m@np.conj(m))*m*0)  # placeholder
    return np.array(r)
def res2(x):
    u,d,p,e,Z,m=unpack(x); r=[u@u, d@d, u@p, d@e, p@p-1, e@e-1, lu@u-1, ld@d-1, m.sum(), lm@m-1]
    r+=list(Z.sum(0)-m)
    u4,d4,p4,e4=H@u,H@d,H@p,H@e
    K=[np.outer(u4,[1,1,0,0,0]), np.outer(p4+e4,[1,0,0,0,0])+np.outer(p4-e4,[0,1,0,0,0]), np.outer(d4,[1,-1,0,0,0]), Z]
    for w in Wpts:
        Y=sum(wi*Ki for wi,Ki in zip(w,K)); cv=C(Y)
        r+=list(cv[1:]*m[0]-cv[0]*m[1:])     # c(Y) parallel to m (2x2 minors with the first entry)
        r.append(cv.sum())
    return np.array(r)
nv=37
for st in range(nst):
    x=rng.normal(size=nv)+1j*rng.normal(size=nv); lam=1e-3; f=res2(x); nf=np.linalg.norm(f)
    for it in range(250):
        if nf<1e-11: break
        J=np.zeros((len(f),nv),complex)
        for k in range(nv):
            ee=np.zeros(nv,complex); ee[k]=1e-7; J[:,k]=(res2(x+ee)-f)/1e-7
        dx=np.linalg.lstsq(J.conj().T@J+lam*np.eye(nv),-J.conj().T@f,rcond=None)[0]; f2=res2(x+dx)
        if np.linalg.norm(f2)<nf: x=x+dx; f=f2; nf=np.linalg.norm(f2); lam=max(lam/3,1e-14)
        else: lam*=4
    u,d,p,e,Z,m=unpack(x); mn=m/m[np.argmax(abs(m))]
    print('start %d res %.1e  m = %s'%(st,nf,np.round(mn,4)),flush=True)
