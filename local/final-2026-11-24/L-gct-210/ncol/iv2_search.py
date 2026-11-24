# case (a), sub-case (iv-2): 3-dim spaces Q of 4x4 matrices with rows in U = {x : sum x = 0, x_0 = x_1} (columns 0, 1 equal),
# Q level (P_1..P_4 = 0) and all four 3x4 row deletions level (P_1..P_3 = 0).  If such Q exists, L' = (Q|0) + (0|1^perp) is a (6,<=2) space.
# usage: python3 -I iv2_search.py MODE s0 s1 tmax     MODE = iv2 (target) | free (control: rows in V4, no equal columns, dim 3)
import sys, itertools, time, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows'); from clm import solve
def per(M):
    n=M.shape[-1]; s=0
    for p in itertools.permutations(range(n)): s=s+np.prod([M[...,i,p[i]] for i in range(n)],axis=0)
    return s
def Pk(M,k):   # sum of k x k subpermanents of p x 4 matrices, batched
    p=M.shape[-2]; s=0
    for R in itertools.combinations(range(p),k):
        for C in itertools.combinations(range(4),k): s=s+per(M[...,list(R),:][...,:,list(C)])
    return s
class P:
    def __init__(self,mode,seed,N=120):
        rng=np.random.default_rng(seed); self.rng=rng
        if mode=='iv2': Ub=np.array([[1,1,-2,0],[0,0,1,-1]],complex)
        else: Ub=np.array([[1,-1,0,0],[0,1,-1,0],[0,0,1,-1]],complex)
        k=len(Ub); B=[]
        for i in range(4):
            for a in range(k):
                M=np.zeros((4,4),complex); M[i]=Ub[a]; B.append(M.ravel())
        B=np.array(B); q,_=np.linalg.qr(B.T); B=q.T
        U,_=np.linalg.qr(rng.normal(size=(len(B),len(B)))+1j*rng.normal(size=(len(B),len(B)))); self.B=U@B
        self.n=len(B); self.d=3; self.nvar=3*(self.n-3); self.N=N
        A=rng.normal(size=(N,3))+1j*rng.normal(size=(N,3)); self.A=A/np.linalg.norm(A,axis=1)[:,None]
    def basis(self,z):
        W=z.reshape(3,self.n-3); return (np.concatenate([np.eye(3),W],1)@self.B).reshape(3,4,4)
    def res(self,z):
        Bq=self.basis(z); X=np.einsum('na,aij->nij',self.A,Bq)
        r=[Pk(X,k) for k in (2,3,4)]
        for i in range(4):
            Xi=np.delete(X,i,axis=1); r+= [Pk(Xi,2),Pk(Xi,3)]
        return np.concatenate(r)
    def fun(self,z,jac=True):
        r=self.res(z)
        if not jac: return r
        h=1e-7; J=np.zeros((len(r),self.nvar),complex)
        for v in range(self.nvar):
            dz=np.zeros(self.nvar,complex); dz[v]=h; J[:,v]=(self.res(z+dz)-r)/h
        return r,J
mode=sys.argv[1]; s0,s1=int(sys.argv[2]),int(sys.argv[3]); tmax=float(sys.argv[4])
t0=time.time(); nf=0; nt=0; res=[]
for s in range(s0,s1):
    if time.time()-t0>tmax: break
    Pr=P(mode,s); z,c=solve(Pr,iters=200,tol=1e-12); nt+=1; res.append(c)
    Bq=Pr.basis(z); cond=np.linalg.cond(Bq.reshape(3,-1))
    if c<1e-8 and cond<1e6:
        nf+=1; np.save('iv2_%s_s%d.npy'%(mode,s),Bq); print('%s seed %d res %.1e cond %.1e'%(mode,s,c,cond),flush=True)
print('%s: found %d of %d, smallest %s, t=%.0f'%(mode,nf,nt,np.array2string(np.sort(res)[:5],precision=2),time.time()-t0),flush=True)
