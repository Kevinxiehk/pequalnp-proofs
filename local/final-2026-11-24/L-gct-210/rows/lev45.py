"""4x5 level spaces of dim 6 and 7: unseeded and seeded searches in plain 'level' mode; equal-row classes for 4 rows."""
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np, time, glob
from clm import *
class Mult4(Problem):
    def __init__(self,mu,d,seed=0,N=None):
        k=len(mu); self.p,self.d,self.mode,self.e=4,d,'level',0
        rng=np.random.default_rng(seed); self.rng=rng; n=k*Q
        Emb=np.zeros((n,20)); r=0
        for b,m in enumerate(mu):
            for _ in range(m):
                for j in range(Q): Emb[b*Q+j,r*Q+j]=1
                r+=1
        M=rng.normal(size=(n,n))+1j*rng.normal(size=(n,n)); q,_=np.linalg.qr(M); self.Pi=q@Emb
        self.N=N or 150
        A=rng.normal(size=(self.N,d))+1j*rng.normal(size=(self.N,d)); self.A=A/np.linalg.norm(A,axis=1)[:,None]
        self.nW=d*(n-d); self.R=Rlevel(4); self.nvar=self.nW
def start_level(P,Zs,rng,scale=1.0):
    d=P.d; n=20; Zm=Zs.reshape(len(Zs),n)
    extra=(rng.normal(size=(d-len(Zs),n))+1j*rng.normal(size=(d-len(Zs),n)))*scale/np.sqrt(n)
    Zm=np.concatenate([Zm,extra],0); AB=Zm@P.Pi.conj().T; return np.linalg.solve(AB[:,:d],AB[:,d:]).ravel()
def rc45():
    w=np.exp(2j*np.pi/3); B=[]
    for k in range(4):
        M=np.zeros((4,5),complex); M[3,k]=1; M[3,4]=-1; B.append(M)
    M=np.zeros((4,5),complex); M[:3,0]=[1,w,w*w]; M[:3,1]=-M[:3,0]; B.append(M)
    M=np.zeros((4,5),complex); M[:3,2]=[1,w*w,w]; M[:3,3]=-M[:3,2]; B.append(M)
    return np.array(B)
if __name__=='__main__':
    t0=time.time()
    Zr=rc45(); print('rc45-type (free row + ex1 plane): dim',np.linalg.matrix_rank(Zr.reshape(6,-1)),'level err %.1e'%fresh_level(Zr),'defect sv',np.array2string(defect_dim(Zr)[:5],precision=1)); np.save('rc45.npy',Zr)
    # unseeded level mode
    for d,ns in ((6,10),(7,10)):
        res=[]
        for s in range(ns):
            P=Problem(4,d,'level',0,seed=s); z,c=solve(P,iters=300); res.append(c)
        print('unseeded level 4x5 d=%d: smallest residuals'%d,np.array2string(np.sort(res)[:4],precision=1),'t=%.0f'%(time.time()-t0),flush=True)
    # seeded: 5-dim subspace of known 6-dim -> 6 (calibration), 6 -> 7 (target)
    seeds=[Zr]+[np.load(f) for f in sorted(glob.glob('clm_p4_d6_defect3_s*.npy'))+sorted(glob.glob('seed_d6_e3_t*.npy'))]
    for (take,d) in ((5,6),(6,7)):
        res=[]
        for tr in range(15):
            Zs=seeds[tr%len(seeds)]; rng=np.random.default_rng(500+tr)
            if take<len(Zs):
                C=rng.normal(size=(take,len(Zs)))+1j*rng.normal(size=(take,len(Zs))); Zs=np.einsum('kc,cab->kab',C,Zs)
            P=Problem(4,d,'level',0,seed=700+tr); z,c=solve(P,z0=start_level(P,Zs,P.rng,scale=[1.0,0.3,3.0][tr%3]),iters=300); res.append(c)
        print('seeded level 4x5: %d-dim (sub)space of a known 6-dim space + random -> d=%d: found %d of %d; smallest residuals'%(take,d,sum(r<1e-9 for r in res),len(res)),np.array2string(np.sort(res)[:4],precision=1),'t=%.0f'%(time.time()-t0),flush=True)
    for mu,d in (((3,1),4),((3,1),5),((2,2),5),((2,2),6),((2,1,1),5),((2,1,1),6)):
        res=[]
        for s in range(8):
            P=Mult4(mu,d,seed=s); z,c=solve(P,iters=300); res.append(c)
        print('equal-row class mu=%s: dim L_mu=%d (4x5 dim %d): smallest residuals'%(mu,d,d+4-len(mu)),np.array2string(np.sort(res)[:3],precision=1),flush=True)
