# (CC3): column-centred 3x5 level spaces S of dim D with defect dimension <= E (deletion vectors = 3x4 level polynomials - 24).
# 3x5 level: P_1 = P_2 = P_3 = 0.  usage: python3 -I cc3_search.py D E s0 s1 tmax
import sys, itertools, time, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows'); from clm import solve
def per(M):
    n=M.shape[-1]; s=0
    for p in itertools.permutations(range(n)): s=s+np.prod([M[...,i,p[i]] for i in range(n)],axis=0)
    return s
def Pk(M,k):
    p,q=M.shape[-2],M.shape[-1]; s=0
    for R in itertools.combinations(range(p),k):
        for C in itertools.combinations(range(q),k): s=s+per(M[...,list(R),:][...,:,list(C)])
    return s
class P:
    def __init__(self,D,E,seed,N=70):
        rng=np.random.default_rng(seed); self.rng=rng; self.D=D; self.E=E
        B=[]
        for i in range(2):
            for j in range(5):
                M=np.zeros((3,5)); M[i,j]=1; M[2,j]=-1; B.append(M.ravel())
        B=np.array(B,complex); q,_=np.linalg.qr(B.T); B=q.T
        U,_=np.linalg.qr(rng.normal(size=(10,10))+1j*rng.normal(size=(10,10))); self.B=U@B
        F=np.array([[1,-1,0,0,0],[1,1,-2,0,0],[1,1,1,-3,0],[1,1,1,1,-4]],complex); F/=np.linalg.norm(F,axis=1)[:,None]
        Uf,_=np.linalg.qr(rng.normal(size=(4,4))+1j*rng.normal(size=(4,4))); self.F=Uf@F   # orthonormal basis of 1^perp
        self.nW=D*(10-D); self.nT=max(E,0)*(4-max(E,0)); self.nvar=self.nW+self.nT; self.N=N
        A=rng.normal(size=(N,D))+1j*rng.normal(size=(N,D)); self.A=A/np.linalg.norm(A,axis=1)[:,None]
    def basis(self,z):
        W=z[:self.nW].reshape(self.D,10-self.D); return (np.concatenate([np.eye(self.D),W],1)@self.B).reshape(self.D,3,5)
    def res(self,z):
        Bq=self.basis(z); X=np.einsum('na,aij->nij',self.A,Bq)
        r=[Pk(X,2),Pk(X,3)]
        dv=np.stack([2*Pk(np.delete(X,j,axis=2),2)+Pk(np.delete(X,j,axis=2),3) for j in range(5)],1)   # (N,5) degree 2+3 parts
        d2=np.stack([Pk(np.delete(X,j,axis=2),2) for j in range(5)],1); d3=np.stack([Pk(np.delete(X,j,axis=2),3) for j in range(5)],1)
        Fd=self.F.conj().T
        for dd in ((d2,d3) if self.E>=0 else ()):
            c=dd@Fd                                   # coordinates in the 1^perp basis (N,4)
            if self.E==0: r.append(c.ravel())
            else:
                T=z[self.nW:].reshape(self.E,4-self.E); r.append((c[:,self.E:]-c[:,:self.E]@T).ravel())
            r.append(dd.sum(1))
        return np.concatenate([np.ravel(x) for x in r])
    def fun(self,z,jac=True):
        r=self.res(z)
        if not jac: return r
        h=1e-7; J=np.zeros((len(r),self.nvar),complex)
        for v in range(self.nvar):
            dz=np.zeros(self.nvar,complex); dz[v]=h; J[:,v]=(self.res(z+dz)-r)/h
        return r,J
if __name__=='__main__':
    D,E,s0,s1=[int(a) for a in sys.argv[1:5]]; tmax=float(sys.argv[5])
    t0=time.time(); nf=0; nt=0; res=[]
    for s in range(s0,s1):
        if time.time()-t0>tmax: break
        Pr=P(D,E,s); z,c=solve(Pr,iters=200,tol=1e-12); nt+=1; res.append(c)
        Bq=Pr.basis(z); cond=np.linalg.cond(Bq.reshape(D,-1))
        if c<1e-8 and cond<1e6:
            nf+=1; np.save('cc3_d%d_e%d_s%d.npy'%(D,E,s),Bq); print('D=%d E<=%d seed %d res %.1e cond %.1e'%(D,E,s,c,cond),flush=True)
    print('cc3 D=%d E<=%d: found %d of %d, smallest %s, t=%.0f'%(D,E,nf,nt,np.array2string(np.sort(res)[:5],precision=2),time.time()-t0),flush=True)
