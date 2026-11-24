# (EXT) check: every extremal (e+3,e) 4x5 level space has a deletable line of its own (deletable row or neutral column)?
import sys,glob; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np
from clm import *
RD=Rdel()
def lines(Z,n=60,seed=3):
    rng=np.random.default_rng(seed); d=Z.shape[0]
    A=rng.normal(size=(n,d))+1j*rng.normal(size=(n,d)); A/=np.linalg.norm(A,axis=1)[:,None]
    X=np.einsum('nk,kab->nab',A,Z); G,_=G_and_loo(X)
    lev=np.abs(G@Rlevel(4).T).max()
    col=[np.abs(np.einsum('ns,ks->nk',G,RD[:,j,:])).max() for j in range(5)]   # neutral column j: p_k(Y)_j = 0
    row=[]
    for i in range(4):
        G3,_=G_and_loo(X[:,[r for r in range(4) if r!=i],:]); row.append(np.abs(G3@Rlevel(3).T).max())
    sv=defect_dim(Z); e=int((sv>1e-4).sum())
    return lev,np.array(row),np.array(col),e
if __name__=='__main__':
    tot=0; bad=[]; tab={}
    for pat in sys.argv[1:]:
        for f in sorted(glob.glob(pat)):
            Z=np.load(f); d=Z.shape[0]; lev,row,col,e=lines(Z)
            if d!=e+3: continue
            tot+=1; tol=1e-5
            dr=[i for i in range(4) if row[i]<tol]; nc=[j for j in range(5) if col[j]<tol]
            key=(d,e,len(dr),len(nc)); tab[key]=tab.get(key,0)+1
            if not dr and not nc: bad.append((f,lev,row.min(),col.min()))
    print('extremal spaces:',tot); 
    for k in sorted(tab): print('  (d,e,#deletable rows,#neutral cols)=',k,':',tab[k])
    print('without deletable line:',len(bad)); 
    for b in bad: print('   ',b)
