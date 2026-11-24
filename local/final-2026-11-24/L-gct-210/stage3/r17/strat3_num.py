# Round 17: numerical probe of (PR3) STRATUM (III): X = span(x1, x2, x3), x1 = (0, v1, w1), x2 = (0, v2, w2) (the 2-dim kernel K_0), x3 = (p, r1, r2);
# level of X, defect <= 2 via Z = span(z1, z2) in 1^perp orthogonal to all deletion vectors (z's: Gram hinge), hinges: v1^v2 != 0, w1^w2 != 0
# (no single-row element inside K_0, rows 1, 2 projections 2-dim), p != 0 (normalised). Report: is p a unit vector (column structure)?
import numpy as np, itertools, sys
seed,NS=int(sys.argv[1]),int(sys.argv[2]); rg=np.random.default_rng(seed)
def sig(M,m,cols):
    tot=0
    for R in itertools.combinations(range(M.shape[0]),m):
        for C in itertools.permutations(cols,m): tot=tot+np.prod([M[R[k],C[k]] for k in range(m)])
    return tot
S=rg.normal(size=(12,3))+1j*rg.normal(size=(12,3)); RB=[rg.normal(size=(5,5))+1j*rg.normal(size=(5,5)) for _ in range(3)]
NP_=rg.normal(size=5)+1j*rg.normal(size=5)
def unpack(x):
    v1,w1,v2,w2,p,r1,r2,z1,z2=[x[5*i:5*i+5] for i in range(9)]; return v1,w1,v2,w2,p,r1,r2,z1,z2
def F(x):
    v1,w1,v2,w2,p,r1,r2,z1,z2=unpack(x); out=[]
    B=[np.array([np.zeros(5),v1,w1]),np.array([np.zeros(5),v2,w2]),np.array([p,r1,r2])]
    for a,b,c in S:
        X=a*B[0]+b*B[1]+c*B[2]
        out+=[sig(X,m,range(5)) for m in (1,2,3)]
        for m in (1,2,3):
            dv=np.array([sig(X,m,[q for q in range(5) if q!=j]) for j in range(5)]); out+=[z1@dv,z2@dv]
    out+=[z1.sum(),z2.sum()]
    for k,(u1,u2) in enumerate([(v1,v2),(w1,w2),(z1,z2)]):
        M=np.stack([u1,u2],1); out.append(x[45+k]*np.linalg.det(M.T@RB[k]@M)-1)
    out.append(NP_@p-1)
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
    x,nf=lm(rg.normal(size=48)+1j*rg.normal(size=48))
    v1,w1,v2,w2,p,r1,r2,z1,z2=unpack(x)
    info=''
    if nf<1e-9:
        pn=np.abs(p)/np.abs(p).max(); info='p (normalised moduli) %s'%np.round(pn,4)
        np.save('/home/kevxhk/work/L-gct-210/stage3/r17/s3num_%d_%d.npy'%(seed,st),x)
    print('start %d res %.1e %s'%(st,nf,info),flush=True)
