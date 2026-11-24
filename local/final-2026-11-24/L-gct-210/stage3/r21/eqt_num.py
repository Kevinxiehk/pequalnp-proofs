# Round 21: numerical probe of the EQUAL-t case: H = {(a w, b w, c h): a+b+c = 0} (h_0 = h_1 = w), X = H + C x*, U' = span(w - h, u) contains all
# deletion vectors. MODE 'II' (stratum-(II) hinges r_i not parallel to h_i via random Gram dets) | 'free' (calibration, no stratum hinges).
import numpy as np, itertools, sys
seed,NS,MODE=int(sys.argv[1]),int(sys.argv[2]),sys.argv[3]; rg=np.random.default_rng(seed)
def sig(M,m,cols):
    tot=0
    for R in itertools.combinations(range(M.shape[0]),m):
        for C in itertools.permutations(cols,m): tot=tot+np.prod([M[R[k],C[k]] for k in range(m)])
    return tot
S=rg.normal(size=(12,3))+1j*rg.normal(size=(12,3)); RB=[rg.normal(size=(5,5))+1j*rg.normal(size=(5,5)) for _ in range(4)]
def unpack(x): return x[0:5],x[5:10],x[10:25].reshape(3,5),x[25:30]
NV=30+1+1+(3 if MODE=='II' else 0)
def F(x):
    w,h,r,u=unpack(x); hs=[w,w,h]; out=[]
    U=np.stack([w-h,u],1); Pj=np.eye(5)-U@np.linalg.pinv(U)
    for a,b,e in S:
        X=np.array([a*w,b*w,(-a-b)*h])+e*r
        out+=[sig(X,m,range(5)) for m in (1,2,3)]
        for m in (1,2,3):
            v=np.array([sig(X,m,[c for c in range(5) if c!=j]) for j in range(5)]); out+=list(Pj@v)
    out.append(x[30]*np.linalg.det(U.T@RB[0]@U)-1); out.append(h.sum()-1); out.append(np.array([0.2,-0.3,0.5,0.9,-0.1])@r.ravel()[:5]+np.array([0.4,0.1,-0.7,0.3,0.6])@r.ravel()[5:10]-1)
    if MODE=='II':
        for i in range(3):
            M=np.stack([hs[i],r[i]],1); out.append(x[32+i]*np.linalg.det(M.T@RB[1+i]@M)-1)
    out.append(x[31]*(u@np.array([0.3,0.7,-0.2,0.1,0.5]))-1)
    return np.array(out)
def lm(x,it=200):
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
for st in range(NS):
    x,nf=lm(rg.normal(size=NV)+1j*rg.normal(size=NV)); info=''
    if nf<1e-9:
        w,h,r,u=unpack(x); hs=[w,w,h]
        B=[np.array([w,-w,0*w]),np.array([w,0*w,-h]),r]
        srow=[3-rank(np.array([np.delete(b,i,axis=0).ravel() for b in B]).T) for i in range(3)]
        rp=[rank(np.array([b[i] for b in B])) for i in range(3)]
        cols=[3-rank(np.array([np.delete(b,j,axis=1).ravel() for b in B]).T) for j in range(5)]
        info='single-row %s row-proj %s column-elements %s'%(srow,rp,cols)
    print('start %d res %.1e %s'%(st,nf,info),flush=True)
