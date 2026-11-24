# Round 18: numerics for the X0 core (hinge-free): does X0 = Y_ab + Y_cd have solutions, and are they degenerate (w's or t's dependent =
# single-row elements)? Same charts as x0core.py with UC = 23.
import numpy as np, itertools, sys
seed,NS=int(sys.argv[1]),int(sys.argv[2]); rg=np.random.default_rng(seed)
def sig(M,m,cols):
    tot=0
    for R in itertools.combinations(range(M.shape[0]),m):
        for C in itertools.permutations(cols,m): tot=tot+np.prod([M[R[k],C[k]] for k in range(m)])
    return tot
S=rg.normal(size=(14,4))+1j*rg.normal(size=(14,4))
def unpack(x):
    v1=np.r_[1,0,x[0:3]]; v2=np.r_[0,1,x[3:6]]; u1=np.array([x[6],x[7],1,0,x[8]]); u2=np.array([x[9],x[10],0,1,x[11]])
    w1,w2,t1,t2=x[12:17],x[17:22],x[22:27],x[27:32]; return v1,v2,u1,u2,w1,w2,t1,t2
def F(x):
    v1,v2,u1,u2,w1,w2,t1,t2=unpack(x); out=[]
    for a,b,c,d in S:
        X=np.array([a*v1+b*v2,a*w1+b*w2,c*u1+d*u2,c*t1+d*t2]); out+=[sig(X,m,range(5)) for m in (1,2,3,4)]
    if MODE=='hinge':
        out.append(x[32]*np.linalg.det(np.array([w1,w2])@RB[0]@np.array([w1,w2]).T)-1); out.append(x[33]*np.linalg.det(np.array([t1,t2])@RB[1]@np.array([t1,t2]).T)-1)
    return np.array(out)
MODE=sys.argv[3]; RB=[rg.normal(size=(5,5))+1j*rg.normal(size=(5,5)) for _ in range(2)]; NV=32+(2 if MODE=='hinge' else 0)
def lm(x,it=200):
    lam=1e-2
    for _ in range(it):
        f=F(x); Jm=np.array([(F(x+1e-7*np.eye(NV)[i])-f)/1e-7 for i in range(NV)]).T; nf=np.linalg.norm(f)
        if nf<1e-12: break
        A=Jm.conj().T@Jm; g=Jm.conj().T@f; ok=False
        for _ in range(10):
            dx=np.linalg.solve(A+lam*np.eye(NV),g)
            if np.linalg.norm(F(x-dx))<nf: x=x-dx; lam=max(lam/4,1e-15); ok=True; break
            lam*=4
        if not ok: break
    return x,np.linalg.norm(F(x))
for st in range(NS):
    x,nf=lm(rg.normal(size=NV)+1j*rg.normal(size=NV))
    v1,v2,u1,u2,w1,w2,t1,t2=unpack(x)
    info=''
    if nf<1e-9: info='rank(w1,w2)=%d rank(t1,t2)=%d'%(np.linalg.matrix_rank(np.array([w1,w2]),1e-6),np.linalg.matrix_rank(np.array([t1,t2]),1e-6))
    print('start %d res %.1e %s'%(st,nf,info),flush=True)
