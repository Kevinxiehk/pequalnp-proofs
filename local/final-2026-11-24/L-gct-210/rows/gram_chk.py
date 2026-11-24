"""Lemma B' (general e): for a 4x5 matrix Y with columns y_j, c_j = sum of column j, s = row sums (sum s = 0),
   b_j(Y) := 2(y_j - c_j/4 * 1) - s  (in V_4).  Identity:  |b_j|^2 = |s|^2 + 3 c_j^2 - 4 p_2(Y)_j,  p_2(Y)_j = P_2(Y minus column j),
   valid whenever P_1(Y) = 0 (sum of all entries 0).  Hence on a level space L' the quadratic form
   Y -> |s(Y)|^2 + 3 c_j(Y)^2 - 4 p_2(Y)_j has rank <= 3 for every column j."""
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np, glob, itertools
from lib import Pk_rect
rng=np.random.default_rng(0)
# identity at random points with total sum zero
err=0
for _ in range(20):
    Y=rng.normal(size=(4,5))+1j*rng.normal(size=(4,5)); Y-=Y.mean()
    s=Y.sum(1); c=Y.sum(0)
    for j in range(5):
        b=2*(Y[:,j]-c[j]/4)-s
        err=max(err,abs(b@b-(s@s+3*c[j]**2-4*Pk_rect(np.delete(Y,j,axis=1),2))),abs(b.sum()))
print('identity |b_j|^2 = |s|^2 + 3c_j^2 - 4 p_2(Y)_j at 20 random sum-zero points: max error %.1e'%err)
# rank of the form on the example spaces
worst={}
for f in sorted(glob.glob('clm_p4_d*_defect*_s*.npy'))+sorted(glob.glob('seed_d*_e*_t*.npy')):
    Z=np.load(f); d=len(Z); u,sv,vh=np.linalg.svd(Z.reshape(d,-1),full_matrices=False); Z=vh.reshape(d,4,5)
    S=Z.sum(2); C=Z.sum(1)
    for j in range(5):
        Bj=2*(Z[:,:,j]-C[:,j][:,None]/4)-S           # (d,4): b_j of basis elements
        Gram=Bj@Bj.T                                   # bilinear Gram of the form on L'
        r=int(np.sum(np.linalg.svd(Gram,compute_uv=False)>1e-8))
        worst[(d,)]=max(worst.get((d,),0),r)
print('max rank over columns of the column forms on the example spaces, by dim L\':',worst,'(must be <= 3)')
