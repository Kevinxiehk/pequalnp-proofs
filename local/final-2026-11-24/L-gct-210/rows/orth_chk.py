import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np, glob, itertools
from clm import *
rng=np.random.default_rng(0)
def analyse(f):
    Z=np.load(f); d=len(Z)
    u,s,vh=np.linalg.svd(Z.reshape(d,-1),full_matrices=False); Z=vh.reshape(d,4,5)
    # defect dim
    A=rng.normal(size=(200,d))+1j*rng.normal(size=(200,d)); X=np.einsum('nk,kab->nab',A,Z); G,_=G_and_loo(X)
    pk=np.einsum('ns,kjs->nkj',G,Rdel()).reshape(-1,5); sv=np.linalg.svd(pk,compute_uv=False); e=int(np.sum(sv>1e-7*max(sv[0],1e-3)))
    if sv[0]<1e-7: e=0
    # row-sum-zero part
    Rs=Z.sum(2)                      # (d,4)
    u,s,vh=np.linalg.svd(Rs); qs=int(np.sum(s>1e-8)); Ms=np.einsum('kc,cab->kab',u[:,qs:].conj().T,Z)   # coefficients c with c^T Rs = 0
    # check
    assert len(Ms)==0 or np.abs(Ms.sum(2)).max()<1e-7
    n=len(Ms); pair=0; trip=0
    for _ in range(20):
        if n==0: break
        c=rng.normal(size=n)+1j*rng.normal(size=n); c/=np.linalg.norm(c); Y=np.einsum('k,kab->ab',c,Ms)
        for i,k in itertools.combinations(range(4),2): pair=max(pair,abs(Y[i]@Y[k]))
        for T in itertools.combinations(range(4),3): trip=max(trip,abs((Y[T[0]]*Y[T[1]]*Y[T[2]]).sum()))
    return d,e,qs,n,pair,trip
tab={}
for pat in ('clm_p4_d3_defect0_s*.npy','clm_p4_d4_defect1_s*.npy','seed_d4_e1_t*.npy','clm_p4_d5_defect2_s*.npy','seed_d5_e2_t*.npy','clm_p4_d6_defect3_s*.npy','seed_d6_e3_t*.npy'):
    for f in sorted(glob.glob(pat)):
        d,e,qs,n,pair,trip=analyse(f)
        key=(d,e,qs,n,'orth' if pair<1e-7 else 'NON-orth','trip0' if trip<1e-7 else 'trip!=0')
        tab[key]=tab.get(key,0)+1
print('(dim L\', e, q_s, dim L\'_s, rows of L\'_s pairwise orthogonal?, triple sums vanish?) : count')
for k in sorted(tab): print('  ',k,':',tab[k])
