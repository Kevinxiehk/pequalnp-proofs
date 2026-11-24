# Round 10: invariants of the known all-2 space clm_p4_d5_defect2_s9: (Q4) P_a P_b P_c P_d = 0 in A_4?  rank of sigma_2 on H = ker sigma_1 in (+) e_r P_r.
import sys, itertools, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r9'); from t1_c52 import rank
Z=np.load('/home/kevxhk/work/L-gct-210/rows/clm_p4_d5_defect2_s9.npy'); d=len(Z)
P=[]
for r in range(4):
    u,s,vh=np.linalg.svd(Z[:,r,:]); P.append(vh[:2])          # orthonormal (Hermitian) basis of the row space; spans the plane
def perm(A): return sum(np.prod([A[i,p[i]] for i in range(len(p))]) for p in itertools.permutations(range(len(A))))
mx=0
for ch in itertools.product(range(2),repeat=4):
    Mx=np.array([P[r][ch[r]] for r in range(4)])
    for S in itertools.combinations(range(5),4): mx=max(mx,abs(perm(Mx[:,list(S)])))
print('max |4x4 subperm| over P_a x P_b x P_c x P_d basis choices: %.2e  (planes normalised, so O(1) means (Q4) fails)'%mx)
# sigma_2 on V8 = (+) e_r P_r : Q(x) = sum_{r<r'} x_r^T (J - I) x_r'
B=[p.T for p in P]; JI=np.ones((5,5))-np.eye(5); Qm=np.zeros((8,8),complex)
for r in range(4):
    for q in range(4):
        if r!=q: Qm[2*r:2*r+2,2*q:2*q+2]=0.5*B[r].T@JI@B[q]
s1=np.concatenate([B[r].T@np.ones(5) for r in range(4)])          # sigma_1 as a linear form on V8
Hb=np.linalg.svd(s1[None,:])[2][1:].T                               # basis of H = ker sigma_1 (8 x 7), bilinear null space
QH=Hb.T@Qm@Hb; print('rank sigma_2 on V8 = %d, on H (dim %d) = %d  (5-dim isotropic subspace needs rank <= 2(dimH - 5) = %d)'%(rank(Qm,1e-8),Hb.shape[1],rank(QH,1e-8),2*(Hb.shape[1]-5)))
print('row-projection singular values:'); 
for r in range(4): print('  row',r,np.round(np.linalg.svd(Z[:,r,:],compute_uv=False),9))
print('sv of sigma_2 on H:',np.round(np.linalg.svd(QH,compute_uv=False),9))
# sigma_2 restricted to L' itself (coordinates in V8): should vanish if L' is level
Lc=np.array([np.concatenate([P[r].conj()@Z[k,r,:] for r in range(4)]) for k in range(d)])   # coords (P rows orthonormal)
print('max |sigma_2| on L\' (in V8 coordinates): %.1e'%np.abs(Lc@Qm@Lc.T).max())
