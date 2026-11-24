# Round 13: re-classification of the 19 rows-team (6,3) spaces with a tolerance adapted to their stored precision (~1e-6): sub-supported parts and
# genuine pieces computed with relative tolerance TOL (default 1e-4).  (The 1e-7 census of round 11/12 under-counted line elements for these files.)
import sys, glob; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from ext6 import F45
TOL=float(sys.argv[1]) if len(sys.argv)>1 else 1e-4
def null(A,tol):
    u,s,vh=np.linalg.svd(A); r=int((s>tol*max(1e-300,s[0] if len(s) else 1)).sum()); return vh[r:].conj()
def sub(M,mask):
    A=M.reshape(len(M),-1)[:,~mask.ravel()].T; Cn=null(A,TOL); return np.einsum('kc,cab->kab',Cn,M) if len(Cn) else np.zeros((0,4,5))
def span(A):
    if len(A)==0: return np.zeros((0,20),complex)
    u,s,vh=np.linalg.svd(A.reshape(len(A),-1)); return vh[:int((s>TOL*s[0]).sum())]
def rk(A): return len(span(A))
for f in sys.argv[2:]:
    M=np.load(f); M=M/np.abs(M).max(); u,s,vh=np.linalg.svd(M.reshape(6,-1)); M=vh[:6].reshape(6,4,5)
    C=np.random.default_rng(0).normal(size=(20,6)); lev=np.abs(F45(np.einsum('nk,kij->nij',C,M))-120).max()
    L=[]
    for i in range(4):
        m=np.zeros((4,5),bool); m[i]=True; L.append(sub(M,m))
    for c in range(5):
        m=np.zeros((4,5),bool); m[:,c]=True; L.append(sub(M,m))
    Lin=span(np.concatenate([l.reshape(len(l),-1) for l in L if len(l)]+[np.zeros((0,20))],0)); e=len(Lin)
    parts=[]
    for (kind,a,b) in [('R',r,j) for r in range(4) for j in range(r+1,4)]+[('C',a,b) for a in range(5) for b in range(a+1,5)]:
        m=np.zeros((4,5),bool)
        if kind=='R': m[a]=True; m[b]=True
        else: m[:,a]=True; m[:,b]=True
        P=sub(M,m)
        if len(P)==0: continue
        g=rk(np.concatenate([Lin,span(P)],0))-e
        if g>0: parts.append('%s%d%d:g%d'%(kind,a,b,g))
    print('%-28s lev %.0e e=%d rows %s cols %s | %s'%(f.split('/')[-1],lev,e,[len(l) for l in L[:4]],[len(l) for l in L[4:]],' '.join(parts)))
