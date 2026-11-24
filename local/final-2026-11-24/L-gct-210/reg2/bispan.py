# Structure test (NOTES-reg2 14.9): is a 4x5 space M spanned by its elements supported in at most TWO rows or at most TWO columns ("bi-line
# spanned")?  Also reports the plain line-span rank.  Applied to all saved deletable-row hits dr35_u*_s*.npy (sparse limit when it is level).
import sys, glob; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np, itertools
from a5 import onb, rref_tol
from t import level_err, rank, null
def sub_supported(B,mask):
    A=B.reshape(len(B),-1)[:,~mask.ravel()].T
    if A.shape[0]==0: return B
    Cn=null(A,1e-7); return np.einsum('kc,cab->kab',Cn,B) if len(Cn) else np.zeros((0,)+B.shape[1:])
def spans(B,k):
    P=[]
    for rows in itertools.combinations(range(4),k):
        m=np.zeros((4,5),bool); m[list(rows)]=True; p=sub_supported(B,m)
        if len(p): P.append(p.reshape(len(p),-1))
    for cols in itertools.combinations(range(5),k):
        m=np.zeros((4,5),bool); m[:,list(cols)]=True; p=sub_supported(B,m)
        if len(p): P.append(p.reshape(len(p),-1))
    return rank(np.concatenate(P,0),1e-6) if P else 0
res={}
for f in sorted(glob.glob('dr35_u*_s*.npy')):
    B=onb(np.load(f)); R=onb(rref_tol(B,1e-5))
    if level_err(R,ntest=15)<1e-9: B=R
    l1=spans(B,1); l2=spans(B,2)
    key=(l1==6,l2==6); res.setdefault(key,[]).append(f)
    if l2<6: print('NOT bi-line spanned:',f,'line rank',l1,'bi-line rank',l2)
for k,v in res.items(): print('line-spanned=%s bi-line-spanned=%s : %d files'%(k[0],k[1],len(v)))
