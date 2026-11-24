# Round 10: does the (t2) normal form admit level spaces?  L' = {((al+de) w + be v2, al b1 + be b2, (ga + de) s + et u2, ga d1 + et d2)}
# (s carries its own scale). FORCE = 1: Rabinowitsch for phi, psi injective (random minor combinations) and w, s != 0 (no single-row
# element); FORCE = 0: only phi, psi injective (s = 0 allowed: then (de w,0,0,0) is a single-row element) -- calibration.
# usage: python3 -I t2_lm.py SEED NSTARTS FORCE
import sys, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r9')
seed,NS,FORCE=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]); rg=np.random.default_rng(seed)
from pr2_search import esig
NP=140; PT=rg.normal(size=(NP,4))+1j*rg.normal(size=(NP,4))
R=[rg.normal(size=5)+1j*rg.normal(size=5) for _ in range(12)]
def unpack(x):
    w,v2,b1,b2,s,u2,d1,d2=x[:40].reshape(8,5); return w,v2,b1,b2,s,u2,d1,d2
def basis(x):
    w,v2,b1,b2,s,u2,d1,d2=unpack(x); Z=np.zeros((4,4,5),complex)
    Z[0]=[w,b1,0*w,0*w]; Z[1]=[v2,b2,0*w,0*w]; Z[2]=[0*w,0*w,s,d1]; Z[3]=[0*w,0*w,u2,d2]
    return Z
def F(x):
    w,v2,b1,b2,s,u2,d1,d2=unpack(x); B=basis(x); X=np.einsum('nk,kab->nab',PT,B); t=x[40:]
    def m2(p,q,a,b): return (R[a]@p)*(R[b]@q)-(R[b]@p)*(R[a]@q)
    eq=[R[0]@w-1, R[1]@v2, R[2]@u2]     # gauge: <r0,w> = 1, <r1,v2> = 0 (v2 mod w), <r2,u2> = 0 (u2 mod s)
    eq+=[R[3]@v2-1, R[4]@u2-1]                                           # scales of v2, u2
    eq+=[t[0]*m2(b1,b2,5,6)-1, t[1]*m2(d1,d2,7,8)-1, t[2]*m2(w,v2,5,7)-1, t[3]*m2(s,u2,6,8)-1]   # phi, psi injective, P_a, P_c 2-dim
    if FORCE: eq+=[t[4]*(R[9]@s)-1]                                      # s != 0
    return np.concatenate([esig(X).ravel()/10,np.array(eq)])
NX=45
def J(x,h=1e-7):
    f0=F(x); Jm=np.empty((len(f0),len(x)),complex)
    for i in range(len(x)):
        d=np.zeros(len(x),complex); d[i]=h; Jm[:,i]=(F(x+d)-f0)/h
    return f0,Jm
def lm(x,it=250):
    lam=1e-2; f,Jm=J(x); nf=np.linalg.norm(f)
    for _ in range(it):
        A=Jm.conj().T@Jm; g=Jm.conj().T@f; ok=False
        for _ in range(10):
            d=np.linalg.solve(A+lam*np.eye(len(x)),g); n2=np.linalg.norm(F(x-d))
            if n2<nf: x=x-d; lam=max(lam/4,1e-14); ok=True; break
            lam*=4
        if not ok: break
        f,Jm=J(x); nf=np.linalg.norm(f)
        if nf<1e-12: break
    return x,nf
def rank(A,tol=1e-6):
    s=np.linalg.svd(np.atleast_2d(A),compute_uv=False); return int((s>tol*max(1,s[0])).sum())
for st in range(NS):
    x,nf=lm((rg.normal(size=NX)+1j*rg.normal(size=NX))*0.6)
    if nf<1e-9:
        B=basis(x); d=len(B)
        u=[d-rank(np.array([[B[k][i,j] for k in range(d)] for i in range(4) if i!=r for j in range(5)])) for r in range(4)]
        rp=[rank(B[:,r,:]) for r in range(4)]; w,v2,b1,b2,s,u2,d1,d2=unpack(x)
        Q=rg.normal(size=(60,4))+1j*rg.normal(size=(60,4)); fresh=np.abs(esig(np.einsum('nk,kab->nab',Q,B))).max()
        print('start %d res %.1e dim %d single-row %s row-proj %s |s| %.1e |w| %.1e fresh %.1e'%(st,nf,rank(B.reshape(4,-1)),u,rp,np.linalg.norm(s),np.linalg.norm(w),fresh),flush=True)
        np.save('/home/kevxhk/work/L-gct-210/stage3/r10/x0sol_f%d_%d_%d.npy'%(FORCE,seed,st),B)
    else: print('start %d res %.1e'%(st,nf),flush=True)
