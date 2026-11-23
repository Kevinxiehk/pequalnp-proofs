"""Census of the extremal (e+3,e) example spaces: single-row parts U_i, their span, two-column vectors in C(L'), radical of C,
   zeta_ab parts (elements z(e_a-e_b)^T), row-sum rank, kernel of gamma (column sums)."""
import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/rows')
import numpy as np, glob, itertools
from clm import *
rng=np.random.default_rng(0)
def rank(M,tol=1e-6):
    if M.size==0: return 0
    s=np.linalg.svd(M,compute_uv=False); return int(np.sum(s>tol))
def null_left(M,tol=1e-6):   # coefficient vectors c with c^T M = 0
    u,s,vh=np.linalg.svd(M); r=int(np.sum(s>tol)); return u[:,r:].conj().T
def defect(Z):
    d=len(Z); A=rng.normal(size=(60*d+60,d))+1j*rng.normal(size=(60*d+60,d)); X=np.einsum('nk,kab->nab',A,Z); G,_=G_and_loo(X)
    pk=np.einsum('ns,kjs->nkj',G,Rdel()).reshape(-1,5); u,s,vh=np.linalg.svd(pk,full_matrices=False); e=int(np.sum(s>1e-6)); return e,vh[:e]
def analyse(f):
    Z=np.load(f); d=len(Z); u,s,vh=np.linalg.svd(Z.reshape(d,-1),full_matrices=False); Z=vh.reshape(d,4,5)
    e,Cb=defect(Z)
    Us=[]; udim=[]
    for i in range(4):
        K=null_left(np.delete(Z,i,axis=1).reshape(d,-1)); Ui=np.einsum('kc,cab->kab',K,Z)[:,i,:] if len(K) else np.zeros((0,5)); Us.append(Ui); udim.append(len(Ui))
    allU=np.concatenate(Us) if sum(udim) else np.zeros((0,5)); sumU=rank(allU)
    # two-column vectors in C: e_a - e_b in C  <=> distance to C zero
    P=Cb.conj().T@Cb if e else np.zeros((5,5)); two=[]
    for a,b in itertools.combinations(range(5),2):
        v=np.zeros(5); v[a]=1; v[b]=-1
        if e and np.linalg.norm(v-P@v)<1e-5: two.append(v)
    two=np.array(two) if two else np.zeros((0,5)); r2=rank(two); rtot=rank(np.concatenate([allU,two])) if (len(allU)+len(two)) else 0
    radC=e-rank(Cb@Cb.T) if e else 0
    # zeta parts: elements supported on two columns a,b with y_a = -y_b
    zet=0
    for a,b in itertools.combinations(range(5),2):
        cons=np.concatenate([np.delete(Z,[a,b],axis=2).reshape(d,-1),Z[:,:,a]+Z[:,:,b]],1); zet=max(zet,d-rank(cons))
    qs=rank(Z.sum(2)); kg=d-rank(Z.sum(1))
    return (d,e,tuple(sorted(udim,reverse=True)),sumU,r2,rtot,radC,zet,qs,kg)
if __name__=='__main__':
    tab={}
    for pat in ('clm_p4_d4_defect1_s*.npy','seed_d4_e1_t*.npy','clm_p4_d5_defect2_s*.npy','seed_d5_e2_t*.npy','clm_p4_d6_defect3_s*.npy','seed_d6_e3_t*.npy'):
        for f in sorted(glob.glob(pat)):
            k=analyse(f); tab.setdefault(k,[]).append(f.replace('.npy','').replace('clm_p4_','').replace('defect','e'))
    print('(d, e, single-row dims u_i (sorted), dim sum U_i, dim span{two-column vectors in C}, dim(sum U_i + two-col), dim rad C, max dim zeta_ab, q_s, dim ker gamma) : count [files]')
    for k in sorted(tab): print('  ',k,':',len(tab[k]),tab[k][:4])
