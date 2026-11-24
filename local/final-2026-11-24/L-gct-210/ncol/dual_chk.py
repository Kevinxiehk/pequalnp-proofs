# check of the transposition duality (NOTES-ncol N3) on untwisted spaces with neutral column 4:
#   L' = (Q|0) + (0|X)  ->  L'' = (Q^T|0) + (0|W_0),  W_0 = vectors w in C^4 (columns 0..3) with w perp 1 and w perp C(L').
# expected: L'' level, C(L'') perp X (so e'' <= 3 - dim X).   usage: python3 -I dual_chk.py FILE.npy [dimX]
import sys, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/handoff'); import oracle
B=np.load(sys.argv[1]); d=len(B)
Bf=B.reshape(d,-1); rng=np.random.default_rng(0)
# split: Q-part = matrices with column 4 = 0 ; X-part = column-4-only matrices
colmask=np.zeros((4,5),bool); colmask[:,4]=True
# subspace with column 4 zero:
A=B[:,:,4].reshape(d,4).T            # 4 x d ; kernel -> Q part
u,s,vh=np.linalg.svd(A); r=int((s>1e-8).sum()); K=vh[r:].conj()
Qb=np.einsum('kd,dab->kab',K,B)[:,:,:4]
Xs=[]
for k in range(4):                    # single-column part: basis elements (0|x) in span
    pass
# defect space
C=[]
for t in range(60):
    Y=np.einsum('d,dab->ab',rng.normal(size=d)+1j*rng.normal(size=d),B); C.append(oracle.deletion_vector(Y))
C=np.array(C); u,s,vh=np.linalg.svd(C); e=int((s>1e-6*s[0]).sum()); Cb=vh[:e]   # rows span conj? use bilinear: null of C
# W_0: w in C^4 (cols 0..3), w.1 = 0, w . C_j = 0 (bilinear)
M=np.concatenate([C[:,:4],np.ones((1,4))],0); u,s,vh=np.linalg.svd(M); r=int((s>1e-6*s[0]).sum()); W0=vh[r:].conj()
print('dim L\'=%d, dim Q=%d, e=%d, dim W_0=%d'%(d,len(Qb),e,len(W0)))
L2=[np.concatenate([q.T,np.zeros((4,1))],1) for q in Qb]
for w in W0:
    Y=np.zeros((4,5),complex); Y[:,4]=w; L2.append(Y)
L2=np.array(L2); print('L\'\' :',oracle.analyse_4x5(L2)[:3])
