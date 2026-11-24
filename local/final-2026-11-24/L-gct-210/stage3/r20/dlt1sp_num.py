# numerical points of the dim Delta = 1 special-locus component (x* = (r04 e_4, r_1, -r04 e_4 - r_1)); check single-row elements, row projections,
# defect, column elements.
import numpy as np, itertools, sys
rg=np.random.default_rng(int(sys.argv[1]))
def sig(M,m,cols):
    tot=0
    for R in itertools.combinations(range(M.shape[0]),m):
        for C in itertools.permutations(cols,m): tot=tot+np.prod([M[R[k],C[k]] for k in range(m)])
    return tot
S=rg.normal(size=(10,3))+1j*rg.normal(size=(10,3))
def build(x):
    d=np.r_[x[0],x[1],x[2],-x[0]-x[1]-x[2],0]; g1,g2=x[3],x[4]; r04=x[5]; r1=x[6:11]
    h=np.array([np.r_[0,0,0,0,1],np.r_[0,0,0,0,1]+g1*d,np.r_[0,0,0,0,1]+g2*d])
    xs=np.array([r04*np.r_[0,0,0,0,1],r1,-r04*np.r_[0,0,0,0,1]-r1]); return d,h,xs
def F(x):
    d,h,xs=build(x); U=np.stack([d,d*d],1); Pj=np.eye(5)-U@np.linalg.pinv(U); out=[d@d]
    for a,b,e in S:
        X=np.array([a*h[0],b*h[1],(-a-b)*h[2]])+e*xs
        out+=[sig(X,m,range(5)) for m in (1,2,3)]
        for m in (1,2,3):
            v=np.array([sig(X,m,[c for c in range(5) if c!=j]) for j in range(5)]); out+=list(Pj@v)
    out.append(x[11]*x[3]*x[4]*(x[3]-x[4])-1); out.append(np.array([0.3,0.5,-0.2,0.7,1.1])@x[6:11]-1)
    return np.array(out)
NV=12
def lm(x,it=200):
    lam=1e-2
    for _ in range(it):
        f=F(x); nf=np.linalg.norm(f)
        if nf<1e-12: break
        Jm=np.array([(F(x+1e-7*np.eye(NV)[i])-f)/1e-7 for i in range(NV)]).T
        A=Jm.conj().T@Jm; gr=Jm.conj().T@f; ok=False
        for _ in range(10):
            dx=np.linalg.solve(A+lam*np.eye(NV),gr)
            if np.linalg.norm(F(x-dx))<nf: x=x-dx; lam=max(lam/4,1e-15); ok=True; break
            lam*=4
        if not ok: break
    return x,np.linalg.norm(F(x))
def rank(A,t=1e-7):
    s=np.linalg.svd(np.atleast_2d(A),compute_uv=False); return int((s>t*max(1,s[0])).sum())
for st in range(int(sys.argv[2])):
    x,nf=lm(rg.normal(size=NV)+1j*rg.normal(size=NV))
    if nf>1e-9: print('start %d res %.1e'%(st,nf),flush=True); continue
    d,h,xs=build(x)
    B=[np.array([h[0],-h[1],0*h[0]]),np.array([h[0],0*h[0],-h[2]]),xs]   # basis of X: (h0,-h1,0), (h0,0,-h2), x*
    Bm=np.array([b.ravel() for b in B])
    srow=[3-rank(np.array([np.delete(b,i,axis=0).ravel() for b in B]).T) for i in range(3)]
    rp=[rank(np.array([b[i] for b in B])) for i in range(3)]
    cols=[3-rank(np.array([np.delete(b,j,axis=1).ravel() for b in B]).T) for j in range(5)]
    print('start %d res %.1e: single-row %s, row-proj dims %s, column elements per column %s, r1 mod d rank %d'%(st,nf,srow,rp,cols,rank(np.stack([d[:4],xs[1][:4]]))),flush=True)
