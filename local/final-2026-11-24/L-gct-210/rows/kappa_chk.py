import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np, glob, itertools
from clm import *
rng=np.random.default_rng(0)
def rank(M,tol=1e-7):
    if M.size==0: return 0
    s=np.linalg.svd(M,compute_uv=False); return int(np.sum(s>tol*max(1.0,s[0])))
tab={}
for f in sorted(glob.glob('di_p3_d*_e*_s*.npy')):
    Z=np.load(f); d=len(Z); u,s,vh=np.linalg.svd(Z.reshape(d,-1),full_matrices=False); Z=vh.reshape(d,3,5)
    A=rng.normal(size=(300,d))+1j*rng.normal(size=(300,d)); X=np.einsum('nk,kab->nab',A,Z); G,_=G_and_loo(X)
    pk=np.einsum('ns,kjs->nkj',G,Rdel()).reshape(-1,5); e=rank(pk)
    Rs=Z.sum(2); u,s,vh=np.linalg.svd(Rs); qs=int(np.sum(s>1e-8)); Ms=np.einsum('kc,cab->kab',u[:,qs:].conj().T,Z); n=len(Ms)
    kap=[]; rows=[]; pair=0
    for _ in range(60):
        if n==0: break
        c=rng.normal(size=n)+1j*rng.normal(size=n); Y=np.einsum('k,kab->ab',c,Ms)
        Aq,Bq,Cq=Y[1]@Y[2],Y[0]@Y[2],Y[0]@Y[1]; pair=max(pair,abs(Aq),abs(Bq),abs(Cq))
        kap.append(Aq*Y[0]+Bq*Y[1]+Cq*Y[2]); rows+= [Y[0],Y[1],Y[2]]
    kap=np.array(kap) if kap else np.zeros((0,5)); rows=np.array(rows) if rows else np.zeros((0,5))
    uu,ss,vv=np.linalg.svd(pk,full_matrices=False); Cb=vv[:e]              # orthonormal basis of C(L')
    def ext(Vs):
        if Vs.size==0 or np.abs(Vs).max()<1e-9: return e
        return rank(np.concatenate([Cb,Vs/np.abs(Vs).max()]))
    eK=ext(kap); eR=ext(rows)
    key=(d,e,qs,n,'orth' if pair<1e-7 else 'NON-orth','dim(C+K)-e=%d'%(eK-e),'dim(C+Rows)-e=%d'%(eR-e))
    tab[key]=tab.get(key,0)+1
print('3x5 level spaces L\' (-> 4x5):  (d, e, q_s, dim L\'_s, rows of L\'_s orthogonal?, extra dims of kappa-span, of row-span) : count')
for k in sorted(tab): print('  ',k,':',tab[k])
