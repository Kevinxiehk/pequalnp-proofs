# Structure-route experiment (NOTES-reg2 13.6): random 3x5 LEVEL spaces S (F_3(J + Y) = 60 on S, F_3 = sum over injections of 3 rows into 5
# columns) of dimension d, by holomorphic Gauss-Newton in a Grassmannian chart; for each solution: defect e = dim C(S) (C(S) = span of
# N(J'+Y) - 24 in the 4x5 picture with a zero row), and whether S is LINE-SPANNED (spanned by its single-row and single-column elements).
# usage: lev35.py SEED d NSTARTS
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np, itertools
from t import rank, null
rg=np.random.default_rng(int(sys.argv[1])); d=int(sys.argv[2]); ns=int(sys.argv[3])
INJ=np.array(list(itertools.permutations(range(5),3)))
def F35(Y):   # Y (...,3,5)
    A=1+Y; return A[...,0,INJ[:,0]]*A[...,1,INJ[:,1]]*A[...,2,INJ[:,2]]
def F35s(Y): return F35(Y).sum(-1)
def solve(N=None,iters=60):
    nz=d*(15-d); N=N or 3*nz+40
    Q=np.linalg.qr(rg.normal(size=(15,15))+1j*rg.normal(size=(15,15)))[0]   # random chart
    C=rg.normal(size=(N,d))+1j*rg.normal(size=(N,d))
    def basis(z):
        Bc=np.concatenate([np.eye(d),z.reshape(d,15-d)],1)       # d x 15 in chart coordinates
        return (Bc@Q.T).reshape(d,3,5)
    def res(z): B=basis(z); return F35s(np.einsum('nk,kij->nij',C,B))-60
    z=(rg.normal(size=nz)+1j*rg.normal(size=nz))*0.3; r=res(z)
    for it in range(iters):
        h=1e-7; J=np.empty((len(r),nz),complex)
        for a in range(nz):
            zp=z.copy(); zp[a]+=h; J[:,a]=(res(zp)-r)/h
        dz=np.linalg.lstsq(J,-r,rcond=None)[0]; zn=z+dz; rn=res(zn)
        if np.linalg.norm(rn)<np.linalg.norm(r): z,r=zn,rn
        else:
            z=z+0.3*dz; r=res(z)
        if np.linalg.norm(r)<1e-10: break
    return np.linalg.norm(r),basis(z)
def lev_err(B,n=40):
    c=rg.normal(size=(n,len(B)))+1j*rg.normal(size=(n,len(B))); return np.abs(F35s(np.einsum('nk,kij->nij',c,B))-60).max()
def defect(B,n=30):
    V=[]
    for _ in range(n):
        c=rg.normal(size=len(B))+1j*rg.normal(size=len(B)); Y=np.einsum('k,kij->ij',c,B); A=np.vstack([np.ones((1,5)),1+Y])
        V.append([np.sum(np.prod(np.delete(A,j,axis=1)[np.arange(4)[:,None],np.array(list(itertools.permutations(range(4)))).T],axis=0))-24 for j in range(5)])
    return rank(np.array(V),1e-6)
def sub_supported(B,mask):
    d_=len(B); A=B.reshape(d_,-1)[:,~mask.ravel()].T
    if A.shape[0]==0: return B
    Cn=null(A,1e-7); return np.einsum('kc,cab->kab',Cn,B) if len(Cn) else np.zeros((0,3,5))
def line_spanned(B):
    parts=[]
    for i in range(3):
        m=np.zeros((3,5),bool); m[i]=True; parts.append(sub_supported(B,m))
    for j in range(5):
        m=np.zeros((3,5),bool); m[:,j]=True; parts.append(sub_supported(B,m))
    P=[p.reshape(len(p),-1) for p in parts if len(p)]
    r=rank(np.concatenate(P,0),1e-6) if P else 0
    return r,[len(p) for p in parts]
hits=0
for s in range(ns):
    c,B=solve()
    if c<1e-8 and rank(B.reshape(d,-1),1e-6)==d and lev_err(B)<1e-8:
        hits+=1; r,pp=line_spanned(B)
        print('d=%d start %d: e=%d line-span rank %d/%d (row parts %s, col parts %s)'%(d,s,defect(B),r,d,pp[:3],pp[3:]),flush=True)
print('d=%d: %d level spaces in %d starts'%(d,hits,ns))
