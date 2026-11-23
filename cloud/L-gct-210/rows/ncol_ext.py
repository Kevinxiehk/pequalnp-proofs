# independent test of (NCOL): for every 7-dim 5x5 level space found by other agents: deletable line, then neutral line of the 4x5 rest
import sys,glob; sys.path.insert(0,'/home/claude/work/L-gct-210/rows')
import numpy as np
from clm import *
from ext_chk import lines
def lev5(B,n=40,seed=5):
    rng=np.random.default_rng(seed); d=B.shape[0]
    A=rng.normal(size=(n,d))+1j*rng.normal(size=(n,d)); A/=np.linalg.norm(A,axis=1)[:,None]
    X=np.einsum('nk,kab->nab',A,B); G,_=G_and_loo(X); return np.abs(G@Rlevel(5).T).max()
def proj(B,r):
    Y=np.delete(B,r,axis=1); d=Y.shape[0]
    u,s,vh=np.linalg.svd(Y.reshape(d,-1),full_matrices=False); k=int((s>1e-5).sum())
    return vh[:k].reshape(k,4,5)
tab={}; n7=0; nodel=[]
for pat in sys.argv[1:]:
    for f in sorted(glob.glob(pat)):
        try: B=np.load(f)
        except Exception: continue
        if B.shape==(7,25): B=B.reshape(7,5,5)
        if B.ndim!=3 or B.shape!=(7,5,5): continue
        B=B.astype(complex)
        u,s,vh=np.linalg.svd(B.reshape(7,-1),full_matrices=False)
        if s[-1]<1e-6*s[0]: continue
        B=vh.reshape(7,5,5)
        if lev5(B)>1e-6: continue
        n7+=1; found=False
        for tr in (0,1):
            Bt=B.transpose(0,2,1) if tr else B
            for r in range(5):
                Lp=proj(Bt,r); lev,row,col,e=lines(Lp)
                if lev<1e-6:
                    found=True; nc=[j for j in range(5) if col[j]<1e-5]; dr=[i for i in range(4) if row[i]<1e-5]
                    key=(Lp.shape[0],e,len(dr),len(nc)); tab[key]=tab.get(key,0)+1
        if not found: nodel.append(f)
print('7-dim level spaces tested:',n7)
for k in sorted(tab): print('  after deleting the deletable line: (d,e,#deletable rows of L\',#neutral cols of L\')=',k,':',tab[k])
print('no deletable line:',len(nodel),nodel[:5])
