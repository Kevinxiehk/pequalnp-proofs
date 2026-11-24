# for 4x5 spaces: defect dim, column sums, rank of each row projection (zero row?), and whether a row lies in a line
import numpy as np, sys
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/handoff'); import oracle
for f in sys.argv[1:]:
    B=np.load(f).reshape(-1,4,5); d=len(B)
    rng=np.random.default_rng(0); C=[]
    for t in range(40): C.append(oracle.deletion_vector(np.einsum('d,dab->ab',rng.normal(size=d)+1j*rng.normal(size=d),B)))
    s=np.linalg.svd(np.array(C),compute_uv=False); e=int((s>1e-6*s[0]).sum())
    cs=np.abs(B.sum(1)).max()
    rr=[np.linalg.matrix_rank(B[:,i,:],1e-6) for i in range(4)]
    print('%s d=%d e=%d max|colsum|=%.1e row-projection ranks %s'%(f.split('/')[-1],d,e,cs,rr))
