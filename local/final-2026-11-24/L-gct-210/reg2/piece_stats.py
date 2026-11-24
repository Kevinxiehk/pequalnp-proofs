# Round 12, target 3: data for a piece-existence lemma.  For every census space: dims of the two-row pieces P_rj (= 6 - dim pi_kl(M)),
# of the two-column pieces, of the three-row pieces (6 - dim pi_l(M)), and of the row/column projections.
import sys, glob, collections; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from pieces import sub_supported
from ext6 import F45
src=open('/home/kevxhk/work/L-gct-210/reg2/bispan_all.py').read(); files=eval(src.split('files=')[1].split('\n')[0])+sorted(glob.glob('dr35_u*_s*.npy'))
st=collections.Counter(); rowproj=collections.Counter(); minpair=collections.Counter(); colproj=collections.Counter(); sums=collections.Counter()
for f in files:
    try: M=np.load(f)
    except Exception: continue
    if M.ndim!=3 or M.shape[1:]!=(4,5) or np.linalg.matrix_rank(M.reshape(len(M),-1),tol=1e-8)!=6: continue
    M=M/np.abs(M).max(); C=np.random.default_rng(0).normal(size=(20,6))
    if np.abs(F45(np.einsum('nk,kij->nij',C,M))-120).max()>1e-6: continue
    pr=[np.linalg.matrix_rank(M[:,i,:],tol=1e-7) for i in range(4)]; rowproj[tuple(sorted(pr))]+=1
    pc=[np.linalg.matrix_rank(M[:,:,c],tol=1e-7) for c in range(5)]; colproj[tuple(sorted(pc))]+=1
    dp=[]
    for r in range(4):
        for j in range(r+1,4):
            m=np.zeros((4,5),bool); m[r]=True; m[j]=True; dp.append(len(sub_supported(M,m)))
    dq=[]
    for a in range(5):
        for b in range(a+1,5):
            m=np.zeros((4,5),bool); m[:,a]=True; m[:,b]=True; dq.append(len(sub_supported(M,m)))
    minpair[(max(dp),max(dq))]+=1; sums[(sum(dp),sum(dq))]+=1
print('row projection dims (sorted):',dict(rowproj))
print('column projection dims (sorted):',dict(colproj))
print('(max two-row piece, max two-column piece):',dict(minpair))
print('(sum of two-row piece dims, sum of two-column piece dims):',dict(sorted(sums.items())))
