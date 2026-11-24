# Round 17: numerical test of FULL stratum (II) ON THE SPECIAL LOCUS h_0 = e_0 (s = 1): h_1 = (1, h1'), h_2 = (1, h2'); x* = (r_0, r_1, -r_0-r_1).
# Conditions: level of X (sigma_1..3 on samples), c, D_2, D_3 in Delta = span(h_0-h_2, h_1-h_2) (dim 2 hinged), stratum hinges r_i ^ h_i != 0.
# MODE 'full' | 'nodef' (calibration) .
import numpy as np, itertools, sys
seed,NS,MODE=int(sys.argv[1]),int(sys.argv[2]),sys.argv[3]; rg=np.random.default_rng(seed)
def sig(M,m,cols):
    tot=0
    for R in itertools.combinations(range(M.shape[0]),m):
        for C in itertools.permutations(cols,m): tot=tot+np.prod([M[R[k],C[k]] for k in range(m)])
    return tot
S=rg.normal(size=(12,3))+1j*rg.normal(size=(12,3))
RB=rg.normal(size=(5,5))+1j*rg.normal(size=(5,5)); RBs=[rg.normal(size=(5,5))+1j*rg.normal(size=(5,5)) for _ in range(3)]
NR=rg.normal(size=10)+1j*rg.normal(size=10)
NV=8+10+1+3
def unpack(x):
    h=np.zeros((3,5),complex); h[0,0]=1; h[1,0]=1; h[2,0]=1; h[1,1:]=x[:4]; h[2,1:]=x[4:8]
    r=np.zeros((3,5),complex); r[0]=x[8:13]; r[1]=x[13:18]; r[2]=-r[0]-r[1]; return h,r
def F(x):
    h,r=unpack(x); out=[]
    Dl=np.stack([h[0]-h[2],h[1]-h[2]],1); Pj=np.eye(5)-Dl@np.linalg.pinv(Dl)
    for a,b,dd in S:
        X=np.array([a*h[0],b*h[1],(-a-b)*h[2]])+dd*r
        out+=[sig(X,m,range(5)) for m in (1,2,3)]
        if MODE!='nodef':
            for m in (1,2,3):
                v=np.array([sig(X,m,[c for c in range(5) if c!=j]) for j in range(5)]); out+=list(Pj@v)
    out.append(x[18]*np.linalg.det(Dl.T@RB@Dl)-1)
    for i in range(3):
        Mi=np.stack([h[i],r[i]],1); out.append(x[19+i]*np.linalg.det(Mi.T@RBs[i]@Mi)-1)
    out.append(NR@x[8:18]-1)
    return np.array(out)
def J(x,hh=1e-7):
    f0=F(x); Jm=np.empty((len(f0),len(x)),complex)
    for i in range(len(x)):
        d=np.zeros(len(x),complex); d[i]=hh; Jm[:,i]=(F(x+d)-f0)/hh
    return f0,Jm
def lm(x,it=200):
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
    x,nf=lm(rg.normal(size=NV)+1j*rg.normal(size=NV))
    print('start %d res %.1e'%(st,nf),flush=True)
    if nf<1e-9: np.save('/home/kevxhk/work/L-gct-210/stage3/r17/spec_%s_%d_%d.npy'%(MODE,seed,st),x)
