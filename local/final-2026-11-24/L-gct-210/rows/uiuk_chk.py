# check: (1) U_i o U_k inside C (i != k);  (2) for u in U_i and Y in L': c^(i)(Y) o u in C and c^(i)(Y).u = 0  (c^(i) = column sums of rows != i)
import sys,glob; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np
from clm import *
RD=Rdel()
def defect_space(Z,ns=80):
    d=Z.shape[0]; rng=np.random.default_rng(2); A=rng.normal(size=(ns,d))+1j*rng.normal(size=(ns,d)); A/=np.linalg.norm(A,axis=1)[:,None]
    X=np.einsum('nk,kab->nab',A,Z); G,_=G_and_loo(X); pk=np.einsum('ns,kjs->nkj',G,RD).reshape(-1,5)
    u,s,vh=np.linalg.svd(pk,full_matrices=False); e=int((s>1e-4).sum()); return vh[:e],e      # orthonormal rows spanning conj? (pk = u s vh: rows of vh span row space)
def single_row(Z,i,tol=1e-6):
    d=Z.shape[0]; oth=[r for r in range(4) if r!=i]; M=Z[:,oth,:].reshape(d,-1)
    u,s,vh=np.linalg.svd(M.T,full_matrices=True); r=int((s>tol).sum()); K=vh[r:].conj()     # coefficient vectors a with sum a_k Z_k having zero other rows
    return np.einsum('ak,kj->aj',K,Z[:,i,:]) if len(K) else np.zeros((0,5),complex)
def dist(v,Cb):   # distance of v from span of rows of Cb (orthonormal rows of vh: v = sum <v,vh_k^*> ...)
    co=v@Cb.conj().T; return np.linalg.norm(v-co@Cb)/max(1e-300,np.linalg.norm(v))
n=0; m1=0; m2=0; m3=0; npairs=0
for pat in sys.argv[1:]:
    for f in sorted(glob.glob(pat)):
        Z=np.load(f); d=Z.shape[0]; Cb,e=defect_space(Z)
        if d!=e+3: continue
        U=[single_row(Z,i) for i in range(4)]; n+=1
        for i in range(4):
            ci=Z.sum(1)-Z[:,i,:]                                  # (d,5) column sums of rows != i on the basis
            for u in U[i]:
                for c in ci:
                    if np.linalg.norm(c)>1e-8:
                        m2=max(m2,dist(c*u,Cb) if np.linalg.norm(c*u)>1e-8 else 0); m3=max(m3,abs((c*u).sum())/(np.linalg.norm(c)*np.linalg.norm(u)))
                for k in range(4):
                    if k!=i:
                        for v in U[k]:
                            npairs+=1
                            if np.linalg.norm(u*v)>1e-8: m1=max(m1,dist(u*v,Cb))
print('extremal spaces',n,' pairs (u,u\') from different rows',npairs)
print('max rel. distance of u o u\' from C: %.1e;   of c^(i)(Y) o u from C: %.1e;   max |c^(i)(Y).u| (rel): %.1e'%(m1,m2,m3))
print('--- per-file diagnosis of c^(i)(Y) o u in C')
bad=0; good=0
for pat in sys.argv[1:]:
    for f in sorted(glob.glob(pat)):
        Z=np.load(f); d=Z.shape[0]; Cb,e=defect_space(Z)
        if d!=e+3: continue
        mx=0; mu=0
        for i in range(4):
            U=single_row(Z,i); ci=Z.sum(1)-Z[:,i,:]
            for u in U:
                mu=max(mu,dist(u,Cb))
                for c in ci:
                    if np.linalg.norm(c*u)>1e-6: mx=max(mx,dist(c*u,Cb))
        if mx>1e-4: bad+=1; print('   ',f,'d,e=',d,e,'max dist(c o u, C)=%.1e'%mx,' max dist(u, C)=%.1e'%mu)
        else: good+=1
print('files ok',good,'bad',bad)
