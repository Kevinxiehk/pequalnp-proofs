# Round 16: numerical test of the stratum-(II) H-PART system (h_0, h_1, h_2 only): level of H + D_2(H), D_3(H) inside Delta = span(h_0-h_2, h_1-h_2),
# dim Delta = 2 hinged (u * minor01 = 1 after a random column mixing is NOT allowed -- use a random 2x2 minor of a random 5x2 combination? no:
# hinge = u * det(Gram of d_0, d_1 w.r.t. a random bilinear form) = 1).  Normalisation sum(h_2) = 1 (sigma = 1) or random linear form = 1.
import numpy as np, itertools, sys
seed,NS,MODE=int(sys.argv[1]),int(sys.argv[2]),sys.argv[3]; rg=np.random.default_rng(seed)
def sig(M,m,cols):
    tot=0
    for R in itertools.combinations(range(M.shape[0]),m):
        for C in itertools.permutations(cols,m): tot=tot+np.prod([M[R[k],C[k]] for k in range(m)])
    return tot
AB=rg.normal(size=(8,2))+1j*rg.normal(size=(8,2))   # sample points (a,b) for coefficient identities
RB=rg.normal(size=(5,5))+1j*rg.normal(size=(5,5)); NRM=rg.normal(size=15)+1j*rg.normal(size=15)
def F(x):
    h=x[:15].reshape(3,5); u=x[15]; out=[]
    d0=h[0]-h[2]; d1=h[1]-h[2]; Dl=np.stack([d0,d1],1)
    Pj=np.eye(5)-Dl@np.linalg.pinv(Dl)      # projector onto Delta-complement (numerically; fine near solutions with dim Delta = 2)
    for a,b in AB:
        X=np.array([a*h[0],b*h[1],(-a-b)*h[2]])
        out+=[sig(X,m,range(5)) for m in (1,2,3)]
        if MODE!='nodef':
            for m in (2,3):
                v=np.array([sig(X,m,[c for c in range(5) if c!=j]) for j in range(5)])
                out+=list(Pj@v)
    G=Dl.T@RB@Dl; out.append(u*np.linalg.det(G)-1)
    out.append((h[2].sum()-1) if MODE!='free' else NRM@x[:15]-1)
    return np.array(out)
def J(x,hh=1e-7):
    f0=F(x); Jm=np.empty((len(f0),len(x)),complex)
    for i in range(len(x)):
        d=np.zeros(len(x),complex); d[i]=hh; Jm[:,i]=(F(x+d)-f0)/hh
    return f0,Jm
def lm(x,it=250):
    lam=1e-2; f,Jm=J(x); nf=np.linalg.norm(f)
    for _ in range(it):
        A=Jm.conj().T@Jm; g=Jm.conj().T@f; ok=False
        for _ in range(10):
            dd=np.linalg.solve(A+lam*np.eye(len(x)),g); n2=np.linalg.norm(F(x-dd))
            if n2<nf: x=x-dd; lam=max(lam/4,1e-15); ok=True; break
            lam*=4
        if not ok: break
        f,Jm=J(x); nf=np.linalg.norm(f)
        if nf<1e-12: break
    return x,nf
for st in range(NS):
    x,nf=lm(rg.normal(size=16)+1j*rg.normal(size=16))
    print('start %d res %.1e'%(st,nf),flush=True)
    if nf<1e-9: np.save('/home/kevxhk/work/L-gct-210/stage3/r16/st2num_%s_%d_%d.npy'%(MODE,seed,st),x)
