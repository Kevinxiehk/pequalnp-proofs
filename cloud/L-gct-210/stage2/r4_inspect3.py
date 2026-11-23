import sys, numpy as np
sys.path.insert(0,'/home/claude/work/L-gct-210/stage2'); from pairlib import rank
np.set_printoptions(precision=3,suppress=True,linewidth=220)
ex=np.load('/tmp/r4_block_examples.npy')
for F in ex:
    # basis of X: parameters (p_c,p_d) in C^4
    B=[]
    for k in range(4):
        pts=np.zeros(4,complex); pts[k]=1; pc=pts[:2]; pd=pts[2:]; pe=-pc-pd
        B.append(np.stack([F[:,0,:]@pc,F[:,1,:]@pd,F[:,2,:]@pe]))
    B=np.array(B)                                   # (4,3,5)
    types=[(int(sum(np.linalg.norm(F[j,i])>1e-6 for i in range(3))),int((np.linalg.svd(F[j],compute_uv=False)>1e-6).sum())) for j in range(5)]
    zc=[4-rank(np.delete(B,j,axis=2).reshape(4,-1)) for j in range(5)]
    twocol=[4-rank(np.delete(B,[j,l],axis=2).reshape(4,-1)) for j in range(5) for l in range(j)]
    print('column types',types,' dim X =',rank(B.reshape(4,-1)),' single-column dims',zc,' max two-column dim',max(twocol),' column projection dims',[rank(B[:,:,j]) for j in range(5)])
