# Round 10, target 3: dimension of Z_B = {zeta in C^5 : (w,w') -> <w o zeta, B w'> is skew on W} for skew maps B on W = 1^perp (C^5), by rank of B.
import numpy as np
rg=np.random.default_rng(1)
W=np.linalg.svd(np.ones((1,5)))[2][1:]          # 4 x 5 basis of 1^perp (real orthonormal; bilinear form = dot)
def ZB(Bc):
    # Bc: 4x4 coefficient matrix, B w_k = sum_l Bc[l,k] w_l ; conditions: sym part of M_zeta[k,l] = <w_k o zeta, B w_l> vanishes
    BW=(Bc.T@W)                                 # rows: B w_k
    rows=[]
    for k in range(4):
        for l in range(k,4):
            # <w_k o zeta, B w_l> + <w_l o zeta, B w_k> = sum_c zeta_c (w_k[c] BW[l,c] + w_l[c] BW[k,c])
            rows.append(W[k]*BW[l]+W[l]*BW[k])
    A=np.array(rows); s=np.linalg.svd(A,compute_uv=False); r=int((s>1e-9*s[0]).sum()); return 5-r
G=W@W.T
for rk in (4,2):
    for trial in range(3):
        S=rg.normal(size=(4,4))+1j*rg.normal(size=(4,4)); S=S-S.T
        if rk==2:
            u=rg.normal(size=4)+1j*rg.normal(size=4); v=rg.normal(size=4)+1j*rg.normal(size=4); S=np.outer(u,v)-np.outer(v,u)
        Bc=np.linalg.solve(G,S)                 # skew w.r.t. the form: <w_k, B w_l> = (G Bc)[k,l] = S[k,l]
        print('rank B = %d: dim Z_B = %d'%(np.linalg.matrix_rank(S),ZB(Bc)))
