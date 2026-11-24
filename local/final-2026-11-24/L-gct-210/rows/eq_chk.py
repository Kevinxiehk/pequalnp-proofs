import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np, glob, itertools
from clm import *
rng=np.random.default_rng(0)
def rank(M,tol=1e-7):
    if M.size==0: return 0
    s=np.linalg.svd(M,compute_uv=False); return int(np.sum(s>tol))
def defect(Z):
    d=len(Z)
    if d==0: return 0,np.zeros((0,5))
    A=rng.normal(size=(60*d+60,d))+1j*rng.normal(size=(60*d+60,d)); X=np.einsum('nk,kab->nab',A,Z); G,_=G_and_loo(X)
    pk=np.einsum('ns,kjs->nkj',G,Rdel()).reshape(-1,5); u,s,vh=np.linalg.svd(pk,full_matrices=False); e=int(np.sum(s>1e-7)); return e,vh[:e]
def analyse(f):
    Z=np.load(f); d=len(Z); u,s,vh=np.linalg.svd(Z.reshape(d,-1),full_matrices=False); Z=vh.reshape(d,4,5)
    e,Cb=defect(Z); out=[]
    for a,b in itertools.combinations(range(5),2):
        moved = e>0 and np.abs(Cb[:,a]-Cb[:,b]).max()>1e-7
        Dm=Z[:,:,a]-Z[:,:,b]; rD=rank(Dm); u2,s2,v2=np.linalg.svd(Dm); K=np.einsum('kc,cab->kab',u2[:,rD:].conj().T,Z)
        eK,_=defect(K) if len(K) else (0,None)
        out.append((a,b,moved,rD,len(K),eK))
    return d,e,out
summary={}
files=sorted(glob.glob('clm_p4_d*_defect*_s*.npy'))+sorted(glob.glob('seed_d[456]_e*_t*.npy'))
for f in files:
    d,e,out=analyse(f)
    if e==0: continue
    good=[o for o in out if o[2]]
    # induction-tight pairs: defect drop equals codimension:  dim D_ab == e - e(L'_ab)
    tight=[o for o in good if o[3]==e-o[5]]
    mind=min(o[3] for o in good)
    viol=[o for o in good if o[5]>e-1]
    key=(d,e,'min dim D_ab=%d'%mind,'tight pair exists' if tight else 'NO tight pair','EQ ok' if not viol else 'EQ VIOLATED')
    summary[key]=summary.get(key,0)+1
    if not tight or (len(sys.argv)>1 and sys.argv[1] in f): print(f,d,e,[(o[0],o[1],o[3],o[4],o[5]) for o in good])
print('(d, e, min over moving pairs of dim D_ab, tight pair?, Lemma EQ general) : count')
for k in sorted(summary): print('  ',k,':',summary[k])
