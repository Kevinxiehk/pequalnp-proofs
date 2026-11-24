# case (a) of C3: 4x5 spaces L' = (Q|0) (+) (0|1^perp) (full free column 4), dim Q = dq, level, defect inside an unknown
# e-dim subspace of e_4^perp cap 1^perp (e = 2: unknown normal nu; e = 3: no constraint).
# usage: python3 -I caseA_search.py dq e s0 s1 tmax      target: dq=3 e=2 ; calibration: dq=2 e=2 (5,2) and dq=3 e=3 (6,3)
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np, time
from clm import G_and_loo, shiftj, Rdel, solve
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/handoff'); import oracle
class PA:
    def __init__(self,dq,e,seed,N=None):
        rng=np.random.default_rng(seed); self.rng=rng; self.dq=dq; self.e=e
        # 15-dim space of 4x4 matrices with total sum 0, embedded in 4x5 (column 4 = 0)
        B=[]
        for a in range(16):
            M=np.zeros((4,5)); M[a//4,a%4]=1; M[0,0]-=1; B.append(M.ravel())
        B=np.array(B[1:],complex)                          # 15 x 20
        q,_=np.linalg.qr(B.T); P=q.T                       # orthonormal rows
        U,_=np.linalg.qr(rng.normal(size=(15,15))+1j*rng.normal(size=(15,15))); self.P=U@P
        F=[]
        for k in range(3):
            Y=np.zeros((4,5)); Y[k,4]=1; Y[3,4]=-1; F.append(Y.ravel())
        self.Fix=np.array(F,complex)                       # (0|1^perp)
        self.d=dq+3; d=self.d
        self.N=N or max(2*int(np.math.comb(d+3,4)) if hasattr(np,'math') else 300,200)
        A=rng.normal(size=(self.N,d))+1j*rng.normal(size=(self.N,d)); self.A=A/np.linalg.norm(A,axis=1)[:,None]
        self.nW=dq*(15-dq); self.nvar=self.nW+(2 if e==2 else 0); self.Rd=Rdel()
        Fe=np.array([[1,-1,0,0,0],[1,1,-2,0,0],[1,1,1,-3,0]],complex); Fe/=np.linalg.norm(Fe,axis=1)[:,None]
        Uf,_=np.linalg.qr(rng.normal(size=(3,3))+1j*rng.normal(size=(3,3))); self.Fe=Uf@Fe
    def Zfull(self,z):
        W=z[:self.nW].reshape(self.dq,15-self.dq); Qb=np.concatenate([np.eye(self.dq),W],1)@self.P
        return np.concatenate([Qb,self.Fix],0)
    def basis(self,z): return self.Zfull(z).reshape(self.d,4,5)
    def dirs(self,z):
        D=[np.ones(5,complex),np.eye(5)[4].astype(complex)]
        if self.e==2: t=z[self.nW:]; D.append(self.Fe[0]+t[0]*self.Fe[1]+t[1]*self.Fe[2])
        return np.array(D)
    def fun(self,z,jac=True):
        N=self.N; Zf=self.Zfull(z); X=(self.A@Zf).reshape(N,4,5)
        G,loo=G_and_loo(X); pk=np.einsum('ns,kjs->nkj',G,self.Rd)
        Dv=self.dirs(z); nd=len(Dv)
        r=np.einsum('nkj,aj->nka',pk,Dv).reshape(N,-1)
        if not jac: return r.ravel()
        dG=np.stack([np.stack([shiftj(loo[i],j) for j in range(5)],1) for i in range(4)],1)
        dpk=np.einsum('nijs,kms->nkmij',dG,self.Rd).reshape(N,4,5,20)
        dr=np.einsum('nkmx,am->nkax',dpk,Dv).reshape(N,4*nd,20)
        DP=dr@self.P[self.dq:].T
        J=np.einsum('na,nrb->nrab',self.A[:,:self.dq],DP).reshape(N*4*nd,self.nW)
        if self.e==2:
            Jt=np.zeros((N,4,nd,2),complex); Jt[:,:,2,0]=pk@self.Fe[1]; Jt[:,:,2,1]=pk@self.Fe[2]
            J=np.concatenate([J,Jt.reshape(N*4*nd,2)],1)
        return r.ravel(),J
dq,e,s0,s1=[int(a) for a in sys.argv[1:5]]; tmax=float(sys.argv[5])
t0=time.time(); nf=0; ntry=0; res=[]
for s in range(s0,s1):
    if time.time()-t0>tmax: break
    P=PA(dq,e,s,N=300); z,c=solve(P,iters=300); ntry+=1; res.append(c)
    B=P.basis(z); cond=np.linalg.cond(B.reshape(P.d,-1))
    if c<1e-9 and cond<1e6:
        d,lev,ee,sv=oracle.analyse_4x5(B); nf+=1; np.save('caseA_d%d_e%d_s%d.npy'%(P.d,e,s),B)
        print('dq=%d e<=%d seed %d res %.1e cond %.1e oracle: dim %d level %.1e e %d sv %s'%(dq,e,s,c,cond,d,lev,ee,np.array2string(sv[:5],precision=2)),flush=True)
    elif s%5==0: print('  seed %d res %.2e cond %.1e t=%.0f'%(s,c,cond,time.time()-t0),flush=True)
print('caseA dq=%d e<=%d: found %d of %d; smallest residuals %s; t=%.0f'%(dq,e,nf,ntry,np.array2string(np.sort(res)[:5],precision=2),time.time()-t0),flush=True)
