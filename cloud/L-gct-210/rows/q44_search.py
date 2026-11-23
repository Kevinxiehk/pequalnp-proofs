# 4x4 problem via padding: 4x5 level spaces of dim d with column 4 identically ZERO and defect space of dim <= e (unknown).
# (Q^T | 0): its defect is e^col(Q) (row-deletion defect of Q).   usage: d e s0 s1 tmax [save] [cc]
import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/rows')
import numpy as np, time
from clm import *
class PZ(Problem):
    def __init__(self,d,e,seed,cc=False):
        # cc=True: additionally all column sums of the padded 4x5 matrix vanish (i.e. Q is ROW-centred, Q^T column-centred)
        Problem.__init__(self,4,d,'defect',e,seed=seed)
        rng=self.rng; n=20
        idx=[i*5+j for i in range(4) for j in range(4)]; idz=[i*5+4 for i in range(4)]
        if cc:
            f=np.array([[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]])/2.0            # orthonormal basis of 1^perp in C^4 (rows index)
            E=np.zeros((16,20),complex); k=0
            for j in range(4):
                for a in range(3):
                    for i in range(4): E[k,i*5+j]=f[a,i]
                    k+=1
            for j in range(4):
                for i in range(4): E[12+j,i*5+j]=0.5
            M=rng.normal(size=(12,12))+1j*rng.normal(size=(12,12)); q12,_=np.linalg.qr(M)
            Pi=np.zeros((20,20),complex); Pi[:12]=q12@E[:12]; Pi[12:16]=E[12:16]; Pi[np.ix_(range(16,20),idz)]=np.eye(4)
            self.Pi=Pi; self.nb=12-d
        else:
            M=rng.normal(size=(16,16))+1j*rng.normal(size=(16,16)); q16,_=np.linalg.qr(M)
            Pi=np.zeros((20,20),complex); Pi[np.ix_(range(16),idx)]=q16; Pi[np.ix_(range(16,20),idz)]=np.eye(4)
            self.Pi=Pi; self.nb=16-d
        self.mask=np.array([a*(n-d)+b for a in range(d) for b in range(self.nb)]+[self.nW+t for t in range(self.nT)])
        self.nfull=self.nW+self.nT; self.nvar=len(self.mask)
    def expand(self,z):
        zz=np.zeros(self.nfull,complex); zz[self.mask]=z; return zz
    def fun(self,z,jac=True):
        zz=self.expand(z)
        if not jac: return Problem.fun(self,zz,False)
        r,J=Problem.fun(self,zz,True); return r,J[:,self.mask]
    def basis(self,z): return Problem.basis(self,self.expand(z))
if __name__=='__main__':
    d,e,s0,s1=[int(a) for a in sys.argv[1:5]]; tmax=float(sys.argv[5]); save='save' in sys.argv[6:]; cc='cc' in sys.argv[6:]
    t0=time.time(); nf=0; ntry=0; res=[]
    for s in range(s0,s1):
        if time.time()-t0>tmax: break
        P=PZ(d,e,s,cc); z,c=solve(P,iters=250); ntry+=1; res.append(c)
        Z=P.basis(z); cond=np.linalg.cond(Z.reshape(d,-1))
        if c<1e-9 and cond<1e6:
            nf+=1; sv=defect_dim(Z)
            print('d=%d e<=%d seed %d res %.1e cond %.1e |col4| %.0e |colsums| %.0e defect sv %s'%(d,e,s,c,cond,np.abs(Z[:,:,4]).max(),np.abs(Z.sum(1)).max(),np.array2string(sv[:5],precision=2)),flush=True)
            if save: np.save('q44%s_d%d_e%d_s%d.npy'%('cc' if cc else '',d,e,s),Z)
    print('(4x4 via padding%s) dim Q=%d, e^col<=%d: found %d of %d; smallest residuals %s; t=%.0f'%(', centred' if cc else '',d,e,nf,ntry,np.array2string(np.sort(res)[:4],precision=2),time.time()-t0))
