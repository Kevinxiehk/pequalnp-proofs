# 5x5 level spaces L containing an embedded 4x5 level space M (row 4 = 0): L/M is an m-plane in T_1(M)/M.  usage: m SEED files...
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np, itertools
from t import *
from a1 import embed
from a5 import onb
from a6 import T1
from ext6 import perm5
def solve55(Mb,D,m,rg,iters=200,N=400):
    b=len(Mb); q=len(D)
    U,_=np.linalg.qr(rg.normal(size=(q,q))+1j*rg.normal(size=(q,q))); D=np.einsum('ab,bij->aij',U,D)
    C=rg.normal(size=(N,b))+1j*rg.normal(size=(N,b)); S=rg.normal(size=(N,m))+1j*rg.normal(size=(N,m))
    base=np.ones((N,5,5),complex)+np.einsum('nk,kij->nij',C,Mb)
    def res(x):
        X=x.reshape(m,q-m); G=D[:m]+np.einsum('ab,bij->aij',X,D[m:])
        return perm5(base+np.einsum('na,aij->nij',S,G))-120
    x=(rg.normal(size=m*(q-m))+1j*rg.normal(size=m*(q-m)))*0.7; mu=1e-2; r=res(x); c=np.linalg.norm(r)
    for it in range(iters):
        h=1e-6; J=np.empty((N,len(x)),complex)
        for a in range(len(x)):
            xp=x.copy(); xp[a]+=h; J[:,a]=(res(xp)-r)/h
        A=J.conj().T@J; g=J.conj().T@r
        for _ in range(8):
            dx=np.linalg.solve(A+mu*np.eye(len(x)),-g); rn=res(x+dx); cn=np.linalg.norm(rn)
            if cn<c: x=x+dx; r=rn; c=cn; mu=max(mu/5,1e-12); break
            mu*=6
        else: break
        if c<1e-11: break
    X=x.reshape(m,q-m); G=D[:m]+np.einsum('ab,bij->aij',X,D[m:])
    return c/np.sqrt(N),np.concatenate([Mb,G],0)
if __name__=='__main__':
    m=int(sys.argv[1]); rg=np.random.default_rng(int(sys.argv[2]))
    for f in sys.argv[3:]:
        B=onb(np.load(f)); Mb=embed(B); T=T1(Mb,rg,npts=100)
        Q,_=np.linalg.qr(Mb.reshape(len(B),25).T); Tm=T.reshape(len(T),25); X=Tm-(Tm@Q.conj())@Q.T
        u,s,vh=np.linalg.svd(X); r=int((s>1e-7).sum()); D=vh[:r].reshape(r,5,5)
        res=[]; 
        for trial in range(12):
            c,L=solve55(Mb,D,m,rg); res.append(c)
            if c<1e-10:
                Lo=onb(L); 
                # fresh check
                e=0
                for _ in range(40):
                    cc=rg.normal(size=len(Lo))+1j*rg.normal(size=len(Lo)); e=max(e,abs(perm(np.ones((5,5))+np.einsum('k,kab->ab',cc,Lo))-120))
                res[-1]=(c,'fresh level err %.1e, dim %d, row-4 rank %d'%(e,len(Lo),rank(Lo[:,4,:])))
        print('%s: dim T1 = %d, extensions by m = %d: %s'%(f,len(T),m,[x if isinstance(x,tuple) else float('%.2g'%x) for x in res]),flush=True)
