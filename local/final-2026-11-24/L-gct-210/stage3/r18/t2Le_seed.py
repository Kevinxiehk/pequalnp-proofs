# Round 18: numerical probe of the FULL (t2) space L_e of (S3-a): normal form L_e = Y_ab (+) Y_cd (+) C (0, g, 0, h), g in P_b, h in P_d
# (rows a,b,c,d = 0..3; derived from (v + de w, phi v, u + de s, psi u) by subtracting Y-elements). Conditions: level (sigma_1..4) of L_e,
# no single-row elements (hinges: P_a..P_d 2-dim), and DEFECT <= 2: Z = span(z1, z2) in 1^perp orthogonal to all deletion vectors
# sigma_t(x minus column j) (t = 1..4). MODE 'def' (with defect) | 'lev' (calibration: level + hinges only).
import numpy as np, itertools, sys
seed,NS,MODE=int(sys.argv[1]),int(sys.argv[2]),sys.argv[3]; rg=np.random.default_rng(seed)
def sig(M,m,cols):
    tot=0
    for R in itertools.combinations(range(M.shape[0]),m):
        for C in itertools.permutations(cols,m): tot=tot+np.prod([M[R[k],C[k]] for k in range(m)])
    return tot
S=rg.normal(size=(16,5))+1j*rg.normal(size=(16,5)); RB=[rg.normal(size=(5,5))+1j*rg.normal(size=(5,5)) for _ in range(3)]
def unpack(x):
    v1=np.r_[1,0,x[0:3]]; v2=np.r_[0,1,x[3:6]]; u1=np.array([x[6],x[7],1,0,x[8]]); u2=np.array([x[9],x[10],0,1,x[11]])
    w1,w2,t1,t2=x[12:17],x[17:22],x[22:27],x[27:32]; gb=x[32:34]; hd=x[34:36]; z1=x[36:41]; z2=x[41:46]
    return v1,v2,u1,u2,w1,w2,t1,t2,gb,hd,z1,z2
NV=46+3
def F(x):
    v1,v2,u1,u2,w1,w2,t1,t2,gb,hd,z1,z2=unpack(x); out=[]
    g=gb[0]*w1+gb[1]*w2; h=hd[0]*t1+hd[1]*t2
    B=[np.array([v1,w1,0*v1,0*v1]),np.array([v2,w2,0*v1,0*v1]),np.array([0*v1,0*v1,u1,t1]),np.array([0*v1,0*v1,u2,t2]),np.array([0*v1,g,0*v1,h])]
    for co in S:
        X=sum(c*b for c,b in zip(co,B)); out+=[sig(X,m,range(5)) for m in (1,2,3,4)]
        if MODE=='def':
            for m in (1,2,3,4):
                dv=np.array([sig(X,m,[q for q in range(5) if q!=j]) for j in range(5)]); out+=[z1@dv,z2@dv]
    if MODE=='def':
        out+=[z1.sum(),z2.sum()]; M=np.stack([z1,z2],1); out.append(x[48]*np.linalg.det(M.T@RB[2]@M)-1)
    out.append(x[46]*np.linalg.det(np.array([w1,w2])@RB[0]@np.array([w1,w2]).T)-1); out.append(x[47]*np.linalg.det(np.array([t1,t2])@RB[1]@np.array([t1,t2]).T)-1)
    out.append(gb@np.array([0.7,-0.4])+hd@np.array([0.2,1.1])-1)
    return np.array(out)
def lm(x,it=150):
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
X0=np.load(sys.argv[4])
for st in range(NS):
    x0=rg.normal(size=NV)+1j*rg.normal(size=NV); x0[:32]=X0[:32]+0.01*(rg.normal(size=32)+1j*rg.normal(size=32))
    x,nf=lm(x0)
    print('start %d res %.1e'%(st,nf),flush=True)
    if nf<1e-9: np.save('/home/kevxhk/work/L-gct-210/stage3/r18/t2Les_%s_%d_%d.npy'%(MODE,seed,st),x)
