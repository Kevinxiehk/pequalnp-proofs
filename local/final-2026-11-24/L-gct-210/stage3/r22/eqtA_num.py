# numerical points of the equal-t case A partition systems (nS, nF), ka = 0, hinge-free; classify: single-row elements, row projections,
# column elements, and whether some h_i is a coordinate vector.
import numpy as np, itertools, sys
nS,nF,seed,NSt=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4]); rg=np.random.default_rng(seed)
def sig(M,m,cols):
    tot=0
    for R in itertools.combinations(range(M.shape[0]),m):
        for C in itertools.permutations(cols,m): tot=tot+np.prod([M[R[k],C[k]] for k in range(m)])
    return tot
S=rg.normal(size=(12,3))+1j*rg.normal(size=(12,3))
nZ=5-nS-nF
def build(x):
    w=np.r_[x[0:nS],np.ones(nF),np.zeros(nZ)]; d=np.r_[x[nS:2*nS],np.zeros(nF+nZ)]; h=w-d
    r0=x[2*nS:2*nS+5]; r1=x[2*nS+5:2*nS+10]; xs=np.array([r0,r1,-r0-r1]); return w,d,h,xs
NV=2*nS+10+2
def F(x):
    w,d,h,xs=build(x); out=[]
    U=np.stack([d,w*d],1); Pj=np.eye(5)-U@np.linalg.pinv(U)
    for a,b,e in S:
        X=np.array([a*w,b*w,(-a-b)*h])+e*xs
        out+=[sig(X,m,range(5)) for m in (1,2,3)]
        for m in (1,2,3):
            v=np.array([sig(X,m,[c for c in range(5) if c!=j]) for j in range(5)]); out+=list(Pj@v)
    out.append(x[-2]*(d[0]*(w[1]*d[1])-d[1]*(w[0]*d[0]))-1); out.append(x[-1]*np.prod(d[:nS])-1)
    out.append(np.array([0.3,0.5,-0.2,0.7,1.1])@xs[0]+np.array([0.2,-0.6,0.4,0.1,0.9])@xs[1]-1)
    if nF==0: out.append(w.sum()-1)
    return np.array(out)
def lm(x,it=250):
    lam=1e-2
    for _ in range(it):
        f=F(x); nf=np.linalg.norm(f)
        if nf<1e-12: break
        Jm=np.array([(F(x+1e-7*np.eye(NV)[i])-f)/1e-7 for i in range(NV)]).T
        A=Jm.conj().T@Jm; g=Jm.conj().T@f; ok=False
        for _ in range(10):
            dx=np.linalg.solve(A+lam*np.eye(NV),g)
            if np.linalg.norm(F(x-dx))<nf: x=x-dx; lam=max(lam/4,1e-15); ok=True; break
            lam*=4
        if not ok: break
    return x,np.linalg.norm(F(x))
def rank(A,t=1e-7):
    s=np.linalg.svd(np.atleast_2d(A),compute_uv=False); return int((s>t*max(1,s[0])).sum())
for st in range(NSt):
    x,nf=lm(rg.normal(size=NV)+1j*rg.normal(size=NV))
    if nf>1e-9: print('start %d res %.1e'%(st,nf),flush=True); continue
    w,d,h,xs=build(x)
    B=[np.array([w,-w,0*w]),np.array([w,0*w,-h]),xs]
    srow=[3-rank(np.array([np.delete(b,i,axis=0).ravel() for b in B]).T) for i in range(3)]
    rp=[rank(np.array([b[i] for b in B])) for i in range(3)]
    cols=[3-rank(np.array([np.delete(b,j,axis=1).ravel() for b in B]).T) for j in range(5)]
    print('start %d res %.1e: single-row %s, row-proj %s, column elements %s, w = %s'%(st,nf,srow,rp,cols,np.round(w,3)),flush=True)
