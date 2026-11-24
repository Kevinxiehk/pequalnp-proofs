# X2 test (rows COMPUTE X2): (6,3) spaces L' = e_0 (x) C (+) N with a FIXED defect space C (row 0 carries C), defect C(L') inside C.
# usage: python3 -I x2_search.py MODE s0 s1 tmax   MODE = b32 (C = V_012 + V_34, no neutral column)  or  b41 (C = V_0123, control)
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np, time
from clm import G_and_loo, shiftj, Rdel, solve
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/handoff'); import oracle
class PX2:
    def __init__(self,mode,seed,N=300):
        rng=np.random.default_rng(seed); self.rng=rng
        if mode=='b32': Cb=np.array([[1,-1,0,0,0],[1,1,-2,0,0],[0,0,0,1,-1]],complex); w=np.array([2,2,2,-3,-3],complex)
        else:           Cb=np.array([[1,-1,0,0,0],[1,1,-2,0,0],[1,1,1,-3,0]],complex); w=np.array([1,1,1,1,-4],complex)
        self.w=w; E=np.zeros((3,4,5),complex); E[:,0,:]=Cb; self.E=E.reshape(3,20)
        q,_=np.linalg.qr(np.concatenate([self.E.T, rng.normal(size=(20,17))+1j*rng.normal(size=(20,17))],1))
        P2=q[:,3:].T                                   # 17 x 20, complement of e_0 (x) C (unitary complement)
        M=rng.normal(size=(17,17))+1j*rng.normal(size=(17,17)); Uq,_=np.linalg.qr(M); self.P2=Uq@P2
        self.d=6; self.N=N
        A=rng.normal(size=(N,6))+1j*rng.normal(size=(N,6)); self.A=A/np.linalg.norm(A,axis=1)[:,None]
        self.nvar=3*14; self.nW=self.nvar; self.Rd=Rdel()
        self.Wv=np.stack([np.ones(5),w.real if np.allclose(w.imag,0) else w],0).astype(complex)  # (2,5): residual directions
    def Zfull(self,z):
        W=z.reshape(3,14); Nb=np.concatenate([np.eye(3),W],1)@self.P2
        return np.concatenate([self.E,Nb],0)          # 6 x 20
    def basis(self,z): return self.Zfull(z).reshape(6,4,5)
    def fun(self,z,jac=True):
        N=self.N; Zf=self.Zfull(z); X=(self.A@Zf).reshape(N,4,5)
        G,loo=G_and_loo(X)
        pk=np.einsum('ns,kjs->nkj',G,self.Rd)          # (N,4,5)
        r=np.einsum('nkj,aj->nka',pk,self.Wv).reshape(N,-1)
        if not jac: return r.ravel()
        dG=np.stack([np.stack([shiftj(loo[i],j) for j in range(5)],1) for i in range(4)],1)   # (N,4,5,32)
        dpk=np.einsum('nijs,kms->nkmij',dG,self.Rd).reshape(N,4,5,20)
        dr=np.einsum('nkmx,am->nkax',dpk,self.Wv).reshape(N,8,20)
        # dZf/dW: rows 3..5 of Zf = [I|W] P2 -> d row(3+a) / dW[a,b] = P2[3+b]
        DP=dr@self.P2[3:].T                              # (N,8,14)
        Aw=self.A[:,3:]                                  # coefficients of the N-part
        J=np.einsum('na,nrb->nrab',Aw,DP).reshape(N*8,42)
        return r.ravel(),J
mode=sys.argv[1]; s0,s1=int(sys.argv[2]),int(sys.argv[3]); tmax=float(sys.argv[4])
t0=time.time(); nf=0; ntry=0; res=[]
for s in range(s0,s1):
    if time.time()-t0>tmax: break
    P=PX2(mode,s); z,c=solve(P,iters=300); ntry+=1; res.append(c)
    B=P.basis(z); cond=np.linalg.cond(B.reshape(6,-1))
    if c<1e-9 and cond<1e6:
        d,lev,e,sv=oracle.analyse_4x5(B)
        nf+=1; np.save('x2_%s_s%d.npy'%(mode,s),B)
        print('%s seed %d res %.1e cond %.1e oracle: dim %d level %.1e e %d sv %s'%(mode,s,c,cond,d,lev,e,np.array2string(sv[:5],precision=2)),flush=True)
    elif s%5==0: print('  seed %d res %.2e cond %.1e t=%.0f'%(s,c,cond,time.time()-t0),flush=True)
print('X2 %s: found %d of %d; smallest residuals %s; t=%.0f'%(mode,nf,ntry,np.array2string(np.sort(res)[:5],precision=2),time.time()-t0),flush=True)
