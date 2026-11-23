# (SC1): for every single-column element x e_n^T of a 4x5 level space L' (n neutral or not) and every Y in L':
#        <x, s(Y) - y_n> = 0   and   (<x,y_j>)_{j != n} (0 at n) lies in C(L')
# NCOL-P ingredients (e = 1, principal K): Z in ker s:  column n of Z is orthogonal to X_n.
import sys,io,contextlib,glob; sys.path.insert(0,'/home/claude/work/L-gct-210/rows'); sys.argv=sys.argv[:1]+sys.argv[1:]
import numpy as np
from clm import *
RD=Rdel()
def rk(M,tol=1e-5):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol).sum()) if s.size else 0
def defect_space(Z,ns=80):
    d=Z.shape[0]; rng=np.random.default_rng(2); A=rng.normal(size=(ns,d))+1j*rng.normal(size=(ns,d)); A/=np.linalg.norm(A,axis=1)[:,None]
    X=np.einsum('nk,kab->nab',A,Z); G,_=G_and_loo(X); pk=np.einsum('ns,kjs->nkj',G,RD).reshape(-1,5)
    u,s,vh=np.linalg.svd(pk,full_matrices=False); e=int((s>1e-4).sum()); return vh[:e],e
def dist(v,Cb):
    co=v@Cb.conj().T; return np.linalg.norm(v-co@Cb)
m1=m2=m3=0; cnt=0; nn=0; nonneutral=0
for pat in sys.argv[1:]:
    for f in sorted(glob.glob(pat)):
        Z=np.load(f); d=Z.shape[0]; Cb,e=defect_space(Z)
        neutral=[j for j in range(5) if np.abs(Cb[:,j]).max()<1e-5] if e>0 else list(range(5))
        for n in range(5):
            oth=[j for j in range(5) if j!=n]; M=Z[:,:,oth].reshape(d,-1)
            u,s,vh=np.linalg.svd(M.T,full_matrices=True); r=int((s>1e-5).sum()); K=vh[r:].conj()
            X=np.einsum('ak,ki->ai',K,Z[:,:,n])
            if len(X)==0: continue
            nn+=1; nonneutral+= (n not in neutral)
            for x in X:
                x=x/np.linalg.norm(x)
                for k in range(d):
                    Y=Z[k]; sY=Y.sum(1); cnt+=1
                    m1=max(m1,abs(x@(sY-Y[:,n])))
                    v=x@Y; v=v.copy(); v[n]=0; m2=max(m2,dist(v,Cb) if e>0 else np.linalg.norm(v))
print('(SC1) (space,column) pairs with single-column elements:',nn,' of which non-neutral columns:',nonneutral,' tests',cnt)
print('   max |<x, s(Y) - y_n>| = %.1e    max dist((<x,y_j>)_{j!=n}, C) = %.1e'%(m1,m2))
