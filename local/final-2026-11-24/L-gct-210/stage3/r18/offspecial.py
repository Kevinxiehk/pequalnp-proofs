# Round 18: numerical search for solutions of the hinge-free stratum-(II) system ("H-plane + zero-column-sum x*", dim Delta = 2) OFF the special
# locus: hinges u_i * q_i(h_i) = 1 with q_i(h) = sum_{a<b} c_ab h_a h_b (random c: h_i not a multiple of a coordinate vector, generically).
# MODE 'off' (hinged) | 'cal' (no hinges: must find the family (E), x* = w (x) e_j).
import numpy as np, itertools, sys
seed,NS,MODE=int(sys.argv[1]),int(sys.argv[2]),sys.argv[3]; rg=np.random.default_rng(seed)
def sig(M,m,cols):
    tot=0
    for R in itertools.combinations(range(M.shape[0]),m):
        for C in itertools.permutations(cols,m): tot=tot+np.prod([M[R[k],C[k]] for k in range(m)])
    return tot
S=rg.normal(size=(12,3))+1j*rg.normal(size=(12,3)); RB=rg.normal(size=(5,5))+1j*rg.normal(size=(5,5))
CQ=[np.triu(rg.normal(size=(5,5))+1j*rg.normal(size=(5,5)),1) for _ in range(3)]; NR=rg.normal(size=10)+1j*rg.normal(size=10)
NV=25+1+(3 if MODE=='off' else 0)
def F(x):
    h=x[:15].reshape(3,5); r0=x[15:20]; r1=x[20:25]; r=np.array([r0,r1,-r0-r1]); out=[]
    Dl=np.stack([h[0]-h[2],h[1]-h[2]],1); Pj=np.eye(5)-Dl@np.linalg.pinv(Dl)
    for a,b,d in S:
        X=np.array([a*h[0],b*h[1],(-a-b)*h[2]])+d*r
        out+=[sig(X,m,range(5)) for m in (1,2,3)]
        for m in (1,2,3):
            v=np.array([sig(X,m,[c for c in range(5) if c!=j]) for j in range(5)]); out+=list(Pj@v)
    out.append(x[25]*np.linalg.det(Dl.T@RB@Dl)-1); out.append(h[2].sum()-1); out.append(NR@x[15:25]-1)
    if MODE=='off':
        for i in range(3): out.append(x[26+i]*(h[i]@CQ[i]@h[i])-1)
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
for st in range(NS):
    x,nf=lm(rg.normal(size=NV)+1j*rg.normal(size=NV))
    info=''
    if nf<1e-9:
        h=x[:15].reshape(3,5); r0=x[15:20]; r1=x[20:25]; r=np.array([r0,r1,-r0-r1])
        nz=[int((np.abs(h[i])>1e-6*np.abs(h[i]).max()).sum()) for i in range(3)]
        par=[np.linalg.matrix_rank(np.stack([h[i],r[i]]),1e-6) for i in range(3)]
        cols=int((np.abs(r).sum(0)>1e-6*np.abs(r).max()).sum())
        info='nonzeros(h_i)=%s rank(h_i,r_i)=%s #nonzero columns of x*=%d'%(nz,par,cols)
        np.save('/home/kevxhk/work/L-gct-210/stage3/r18/off_%s_%d_%d.npy'%(MODE,seed,st),x)
    print('start %d res %.1e %s'%(st,nf,info),flush=True)
