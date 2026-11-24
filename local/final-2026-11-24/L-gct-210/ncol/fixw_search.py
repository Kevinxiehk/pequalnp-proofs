# (6,3) spaces whose defect space lies in C0 = w^perp cap 1^perp for a FIXED w (isotropic test / neutral control).
# usage: python3 -I fixw_search.py WTAG s0 s1 tmax   WTAG: iso1 = (1,w,w^2,0,0), iso2 = (1,i,-1,-i,0), iso3 = full-support isotropic,
#        ctl = (1,1,1,1,-4) (neutral column, control), b32 = (2,2,2,-3,-3)
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np, time
from clm import *
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/handoff'); import oracle
om=np.exp(2j*np.pi/3)
def iso3():
    # full support isotropic sum-zero: (1, a, b, c, d) with a,b chosen, solve c, d from sum = 0, sum sq = 0
    a,b=0.7+0.2j,-1.3+0.5j; s=-(1+a+b); q=-(1+a*a+b*b)   # c+d = s, c^2+d^2 = q -> cd = (s^2-q)/2
    p=(s*s-q)/2; disc=np.sqrt(s*s-4*p); c=(s+disc)/2; d=(s-disc)/2; return np.array([1,a,b,c,d])
W={'iso1':np.array([1,om,om*om,0,0]),'iso2':np.array([1,1j,-1,-1j,0]),'iso3':iso3(),'ctl':np.array([1,1,1,1,-4.]),'b32':np.array([2,2,2,-3,-3.])}
class PF(Problem):
    def __init__(self,d,w,seed):
        Problem.__init__(self,4,d,'defect',3,seed=seed)
        w=np.asarray(w,complex); assert abs(w.sum())<1e-12
        # basis of C0 = {c : c.1 = 0, c.w = 0} (bilinear), plus f4 completing 1^perp
        A=np.stack([np.ones(5),w]); u,s,vh=np.linalg.svd(A); N=vh[2:].conj()          # rows c with A c = 0 (bilinear)
        q,_=np.linalg.qr(N.T); Cb=q.T                                               # 3 x 5
        f4=w.conj()-np.ones(5)*(w.conj().sum()/5)                                   # completes to 1^perp (hermitian complement direction)
        F=np.concatenate([Cb,f4[None]/np.linalg.norm(f4)],0)
        q2,_=np.linalg.qr(F.T); self.Fb=q2.T; self.Fd=q2.conj().T; self.T0=np.zeros((3,1),complex)
        self.nvar=self.nW; self.w=w
    def fun(self,z,jac=True):
        zz=np.concatenate([z,self.T0.ravel()])
        if not jac: return Problem.fun(self,zz,False)
        r,J=Problem.fun(self,zz,True); return r,J[:,:self.nW]
tag=sys.argv[1]; s0,s1=int(sys.argv[2]),int(sys.argv[3]); tmax=float(sys.argv[4]); w=W[tag]
print('w =',np.round(w,4),' w.w =',np.round((w*w).sum(),12),flush=True)
t0=time.time(); nf=0; nt=0; res=[]
for s in range(s0,s1):
    if time.time()-t0>tmax: break
    P=PF(6,w,s); P.N=300; P.A=P.rng.normal(size=(300,6))+1j*P.rng.normal(size=(300,6)); P.A/=np.linalg.norm(P.A,axis=1)[:,None]
    z,c=solve(P,iters=250); nt+=1; res.append(c)
    Z=P.basis(z); cond=np.linalg.cond(Z.reshape(6,-1))
    if c<1e-9 and cond<1e6:
        d,lev,e,sv=oracle.analyse_4x5(Z); nf+=1; np.save('fixw_%s_s%d.npy'%(tag,s),Z)
        print('%s seed %d res %.1e cond %.1e oracle dim %d level %.1e e %d'%(tag,s,c,cond,d,lev,e),flush=True)
    elif s%5==0: print('  seed %d res %.2e t=%.0f'%(s,c,time.time()-t0),flush=True)
print('fixw %s: found %d of %d; smallest %s; t=%.0f'%(tag,nf,nt,np.array2string(np.sort(res)[:5],precision=2),time.time()-t0),flush=True)
