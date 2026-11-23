import numpy as np, sys, itertools
sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases'); import level
B=np.load('/home/claude/work/L-gct-086/smallcases/sol_n4_d5_full_s0.npy'); print(B.shape)
B=B.reshape(len(B),-1); U,s,Vh=np.linalg.svd(B,full_matrices=False); print('sv',s)
Bo=Vh[:np.sum(s>1e-8)]; k=len(Bo)
rng=np.random.default_rng(0); S=rng.normal(size=(30,k))+1j*rng.normal(size=(30,k))
print('fresh',abs(level.Pk((S@Bo).reshape(-1,4,4))[:,1:]).max())
T=Bo.reshape(k,4,4)
# free row test: dim of L cap (row-r supported)
for r in range(4):
    M=np.delete(T,r,axis=1).reshape(k,-1); ns=k-np.linalg.matrix_rank(M,1e-8); print('row',r,'supported dim',ns, ' col',r, k-np.linalg.matrix_rank(np.delete(T,r,axis=2).reshape(k,-1),1e-8))
# row-zero subspaces
for r in range(4): print('L_r dim', k-np.linalg.matrix_rank(T[:,r,:],1e-8), 'L^c dim', k-np.linalg.matrix_rank(T[:,:,r],1e-8))
