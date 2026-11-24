# 2-dim zero-row column-centred 3x5 level spaces with defect parallel to a FIXED m (well sampled: 40 points for degree <= 3 in 2 vars).
# isotropic coordinates (a, b) in C^5 x C^5; identities: P2 = 3(sum ab - AB), P3 = 6(e3(a)+e3(b)); d2_k, d3_k as in R2.5; residual: d - (d.m*)m/|m|^2.
import numpy as np, itertools, sys
seed=int(sys.argv[1]); nst=int(sys.argv[2]); mode=sys.argv[3]   # mode: 'three' (m = (1,1,1,y,z)) or 'free' (m random generic)
rng=np.random.default_rng(seed)
if mode=='three':
    y=rng.normal()+1j*rng.normal(); m=np.array([1,1,1,y,-3-y])
elif mode=='twotwo':
    y=rng.normal()+1j*rng.normal(); m=np.array([1,1,y,y,-2-2*y])
elif mode=='onezero':
    y=rng.normal()+1j*rng.normal(); z=rng.normal()+1j*rng.normal(); m=np.array([0,1,y,z,-1-y-z])
elif mode=='pq':
    m=np.array([0,0,1,-1,0],complex)
else:
    m=rng.normal(size=5)+1j*rng.normal(size=5); m-=m.mean()
mh=m/np.linalg.norm(m)
def e3(v): return sum(v[i]*v[j]*v[k] for i,j,k in itertools.combinations(range(len(v)),3))
pts=[rng.normal(size=2)+1j*rng.normal(size=2) for _ in range(40)]
def resid(x):
    z=x[:20]+1j*x[20:]; Sb=z.reshape(2,10); out=[]
    for c in pts:
        v=c@Sb; a=v[:5]; b=v[5:]
        out+=[3*((a*b).sum()-a.sum()*b.sum()), 6*(e3(a)+e3(b))]
        d2=np.array([3*((np.delete(a,k)*np.delete(b,k)).sum()-np.delete(a,k).sum()*np.delete(b,k).sum()) for k in range(5)])
        d3=np.array([6*(e3(np.delete(a,k))+e3(np.delete(b,k))) for k in range(5)])
        for d in (d2,d3): out+=list(d-(d@mh.conj())*mh)
    out+=list((Sb@Sb.conj().T-np.eye(2)).ravel())
    out=np.array(out); return np.concatenate([out.real,out.imag])
def jac(x,f0,h=1e-7):
    J=np.zeros((len(f0),len(x)))
    for i in range(len(x)):
        xp=x.copy(); xp[i]+=h; J[:,i]=(resid(xp)-f0)/h
    return J
for st in range(nst):
    x=rng.normal(size=40)*0.5; lam=1e-2; f=resid(x); c=f@f
    for it in range(150):
        J=jac(x,f); g=J.T@f; H=J.T@J
        while True:
            dx=np.linalg.solve(H+lam*np.diag(np.diag(H)+1e-12),-g); xn=x+dx; fn=resid(xn); cn=fn@fn
            if cn<c: x,f,c=xn,fn,cn; lam=max(lam/3,1e-12); break
            lam*=4
            if lam>1e8: break
        if lam>1e8 or c<1e-26: break
    # defect dimension of the solution
    z=x[:20]+1j*x[20:]; Sb=z.reshape(2,10); V=[]
    for c0 in [rng.normal(size=2)+1j*rng.normal(size=2) for _ in range(12)]:
        v=c0@Sb; a=v[:5]; b=v[5:]
        V.append([3*((np.delete(a,k)*np.delete(b,k)).sum()-np.delete(a,k).sum()*np.delete(b,k).sum()) for k in range(5)])
        V.append([6*(e3(np.delete(a,k))+e3(np.delete(b,k))) for k in range(5)])
    sv=np.linalg.svd(np.array(V),compute_uv=False)
    print('%s start %d: residual %.2e  defect sv %s'%(mode,st,c,np.array2string(sv[:2],precision=2)),flush=True)
