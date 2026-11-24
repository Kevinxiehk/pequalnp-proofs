# Round 7: the bi-line pieces of 6-dim 4x5 level spaces.  For each space M (sparse limit when level): L1 = span of single-row and single-column
# parts; for each row pair R and column pair C the piece P = M cap {supported in R (resp. C)}; report the pieces that are NOT inside L1:
# (kind, rows/cols, dim P, dim (P + L1) - dim L1, rank of a generic element of P, shape).  Shapes for a 2-column piece {x e_a + y e_b}:
# 'rank1' if every element has rank 1 (x || y), 'skew' if P/lines is 2-dim and y = A x with A skew (w.r.t. the bilinear form on sum-zero
# vectors) on the projection, 'other' otherwise; the same for 2-row pieces (transposed).
import sys, glob; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np, itertools
from a5 import onb, rref_tol
from t import level_err, rank, null
rg=np.random.default_rng(0)
def sub_supported(B,mask):
    A=B.reshape(len(B),-1)[:,~mask.ravel()].T
    if A.shape[0]==0: return B
    Cn=null(A,1e-7); return np.einsum('kc,cab->kab',Cn,B) if len(Cn) else np.zeros((0,)+B.shape[1:])
def lines(B):
    P=[]
    for i in range(4):
        m=np.zeros((4,5),bool); m[i]=True; P.append(sub_supported(B,m))
    for j in range(5):
        m=np.zeros((4,5),bool); m[:,j]=True; P.append(sub_supported(B,m))
    P=[p.reshape(len(p),-1) for p in P if len(p)]
    return np.concatenate(P,0) if P else np.zeros((0,20))
def shape2(P,axis,idx):
    # P: pieces supported on two columns (axis=1) or two rows (axis=0) with indices idx
    if axis==1: X=P[:,:,idx[0]]; Y=P[:,:,idx[1]]
    else: X=P[:,idx[0],:]; Y=P[:,idx[1],:]
    c=rg.normal(size=len(P))+1j*rg.normal(size=len(P)); x=c@X; y=c@Y
    r1=rank(np.array([x,y]),1e-6)
    if r1<=1: return 'rank1'
    # is y = A x on the piece with A skew?  fit A on the span
    if len(P)>=2:
        # bilinear test: <x_k, y_l> + <x_l, y_k> = 0 for all k,l  (P_2 on the piece is -<x,y> up to the sum terms)
        G=X@Y.T; skew=np.abs(G+G.T).max()<1e-6*max(1,np.abs(G).max())
        return 'skew' if skew else 'other'
    return 'rank2-single'
def analyse(B):
    L1=lines(B); l1=rank(L1,1e-6) if len(L1) else 0; out=[]
    for axis,n in ((0,4),(1,5)):
        for idx in itertools.combinations(range(n),2):
            m=np.zeros((4,5),bool)
            if axis==0: m[list(idx)]=True
            else: m[:,list(idx)]=True
            P=sub_supported(B,m)
            if not len(P): continue
            add=rank(np.concatenate([L1,P.reshape(len(P),-1)],0),1e-6)-l1 if len(L1) else rank(P.reshape(len(P),-1),1e-6)
            if add>0: out.append(('row' if axis==0 else 'col',idx,len(P),add,shape2(P,axis,idx)))
    return l1,out
if __name__=='__main__':
    files=sorted(glob.glob('dr35_u*_s*.npy')+glob.glob('../rows/clm_p4_d6_*.npy')+glob.glob('../rows/nc_d6_*.npy')+glob.glob('../rows/seed_d6_*.npy')+glob.glob('../rows/rc45.npy')+glob.glob('ec_*.npy')+glob.glob('ec2_*.npy')+glob.glob('Mstar2.npy')+glob.glob('M_*.npy')+glob.glob('dr_u3_*.npy')+glob.glob('linespan_other_*.npy')+glob.glob('ext_*.npy')+glob.glob('p21111_hit_*.npy'))
    stats={}
    for f in files:
        B0=np.load(f)
        if B0.ndim!=3 or B0.shape[1:]!=(4,5): continue
        B=onb(B0)
        if len(B)!=6: continue
        R=onb(rref_tol(B,1e-5))
        if level_err(R,ntest=15)<1e-9: B=R
        l1,out=analyse(B)
        if l1<6:
            sig=tuple(sorted((k,dP,a,s) for (k,idx,dP,a,s) in out))
            stats.setdefault(sig,[]).append(f.split('/')[-1])
            print('%-34s line rank %d | non-line pieces: %s'%(f.split('/')[-1],l1,[(k,idx,dP,a,s) for (k,idx,dP,a,s) in out]),flush=True)
    print('\nSIGNATURES (kind, dim P, new dims, shape):')
    for k,v in sorted(stats.items(),key=lambda kv:-len(kv[1])): print('%3d  %s   e.g. %s'%(len(v),k,v[0]))
