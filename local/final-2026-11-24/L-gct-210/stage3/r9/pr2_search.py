# Round 9: numerical probe of (PR2): 5-dim 4x5 level spaces L' inside (+)_r e_r (x) P_r (P_r unknown 2-planes of C^5), i.e. with all
# four row projections of dim <= 2. Holomorphic LM (finite-difference complex Jacobian). Chart: L' = row space of [I_5 | W] Gamma-coordinates
# on C^8 = (+)_r P_r; planes normalised by <al_r,u_r>=1, <be_r,u_r>=0, <al_r,v_r>=0, <be_r,v_r>=1. Residual: sigma_1..sigma_4 of the 4x5
# matrix at N = 2 x 70 random points. Each solution is classified: single-row dims, row-projection dims, fresh-point level error.
# CALIBRATION: clm_p4_d5_defect2_s9 (row projections (2,2,2,2), single-row dims (1,1,0,0)) shows that solutions of this shape exist.
# usage: python3 -I pr2_search.py SEED NSTARTS
import sys, itertools, numpy as np
seed,NS=(int(sys.argv[1]),int(sys.argv[2])) if __name__=='__main__' else (0,0); HNS=int(sys.argv[3]) if (__name__=='__main__' and len(sys.argv)>3) else 0; rg=np.random.default_rng(seed)
# hinges (Rabinowitsch, variables x[55:63]): rank 2 of every row block of Gamma (always); with HNS=1 also no single-row element
RH=[(rg.normal(size=5)+1j*rg.normal(size=5),rg.normal(size=5)+1j*rg.normal(size=5)) for _ in range(4)]
RN=[rg.normal(size=(6,5))+1j*rg.normal(size=(6,5)) for _ in range(4)]
NX=63 if HNS else 59
NP=140; PT=rg.normal(size=(NP,5))+1j*rg.normal(size=(NP,5))
AL=rg.normal(size=(4,5))+1j*rg.normal(size=(4,5)); BE=rg.normal(size=(4,5))+1j*rg.normal(size=(4,5))
def esig(X):   # sigma_k of 4x5 matrices X (N,4,5): coefficients of prod_j (1 + sum_i t_i x_ij) in the squarefree algebra
    N=X.shape[0]; G=np.zeros((N,16),complex); G[:,0]=1
    for j in range(5):
        H=G.copy()
        for i in range(4):
            m=1<<i; idx=[S for S in range(16) if not S&m]
            H[:,[S|m for S in idx]]+=X[:,i,j][:,None]*G[:,idx]
        G=H
    deg=np.array([bin(S).count('1') for S in range(16)])
    return np.stack([G[:,deg==k].sum(1) for k in range(1,5)],1)
def unpack(x):
    U=x[:20].reshape(4,5); V=x[20:40].reshape(4,5); W=x[40:55].reshape(5,3)
    Gm=np.concatenate([np.eye(5),W],1)                       # 5 x 8, columns = (u_a,v_a,u_b,v_b,...)
    B=np.zeros((5,4,5),complex)
    for r in range(4): B[:,r,:]=Gm[:,2*r][:,None]*U[r][None,:]+Gm[:,2*r+1][:,None]*V[r][None,:]
    return B,U,V
def F(x):
    B,U,V=unpack(x); X=np.einsum('nk,kab->nab',PT,B)
    nrm=[]
    for r in range(4): nrm+=[AL[r]@U[r]-1,BE[r]@U[r],AL[r]@V[r],BE[r]@V[r]-1]
    W=x[40:55].reshape(5,3); Gm=np.concatenate([np.eye(5),W],1); hz=[]
    for r in range(4):
        Gr=Gm[:,2*r:2*r+2]; a,b=RH[r]; hz.append(x[55+r]*np.linalg.det(np.array([a@Gr,b@Gr]))-1)
        if HNS:
            O=np.concatenate([Gm[:,2*s_:2*s_+2] for s_ in range(4) if s_!=r],1); hz.append(x[59+r]*np.linalg.det(O@RN[r])-1)
    return np.concatenate([esig(X).ravel()/10,np.array(nrm),np.array(hz)])
def J(x,h=1e-7):
    f0=F(x); Jm=np.empty((len(f0),len(x)),complex)
    for i in range(len(x)):
        d=np.zeros(len(x),complex); d[i]=h; Jm[:,i]=(F(x+d)-f0)/h
    return f0,Jm
def lm(x,it=200):
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
def classify(B):
    d=len(B)
    def ker(rows): return d-rank(np.array([[B[k][i,j] for k in range(d)] for i in rows for j in range(5)]))
    u=[ker([i for i in range(4) if i!=r]) for r in range(4)]; rp=[rank(B[:,r,:]) for r in range(4)]
    Q=rg.normal(size=(60,5))+1j*rg.normal(size=(60,5)); fresh=np.abs(esig(np.einsum('nk,kab->nab',Q,B))).max()
    return u,rp,fresh
if __name__=='__main__':
    res={}
    for st in range(NS):
        x,nf=lm((rg.normal(size=NX)+1j*rg.normal(size=NX))*0.6)
        if nf<1e-9:
            B,U,V=unpack(x); u,rp,fresh=classify(B); key='single-row dims %s, row-proj dims %s'%(sorted(u,reverse=True),sorted(rp)); res[key]=res.get(key,0)+1
            print('start %d residual %.1e  %s  fresh %.1e%s'%(st,nf,key,fresh,'   <-- NO single-row element' if sum(u)==0 else ''),flush=True)
            if fresh<1e-7 and (sum(u)==0 or max(u)>=2): np.save('/home/kevxhk/work/L-gct-210/stage3/r9/pr2_sol_%d_%d.npy'%(seed,st),B)
        else: print('start %d residual %.1e (no convergence)'%(st,nf),flush=True)
    print('SUMMARY seed %d starts %d HNS %d:'%(seed,NS,HNS),res,flush=True)
