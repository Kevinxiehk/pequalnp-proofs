import sys; sys.path.insert(0,"/home/kevxhk/work/L-gct-210/methods")
import numpy as np, itertools
from rlx import coeffs, hess, grad, load_space, setup
n=5
def sub3(g):
    return max(abs(sum(np.prod([g[R[a],C[p[a]]] for a in range(3)]) for p in itertools.permutations(range(3))))
               for R in itertools.combinations(range(5),3) for C in itertools.combinations(range(5),3))
def sub4(g):
    return max(abs(sum(np.prod([g[R[a],C[p[a]]] for a in range(4)]) for p in itertools.permutations(range(4))))
               for R in itertools.combinations(range(5),4) for C in itertools.combinations(range(5),4))
items=[('DCplane(sol_n5_d2)','/home/kevxhk/work/L-gct-086/smallcases/sol_n5_d2_dc_s5.npy'),('W5 DC','W5_DC.npy'),
       ('rank1weight','sp_rank1weight.npy'),('circ4','sp_circ4.npy'),('ex1 DC plane','sp_ex1DC.npy'),
       ('ex1 generic','sp_ex1.npy'),('ex2 generic','sp_ex2.npy'),('L080 generic','sp_L080.npy'),('W5+1 (S4_r1d3)','../numerics/S4_r1d3.npy')]
for name,f in items:
    V=load_space(f); rng=np.random.default_rng(0); c=rng.normal(size=V.shape[0])+1j*rng.normal(size=V.shape[0]); g=(c@V).reshape(n,n); g/=np.linalg.norm(g)
    Hc=coeffs(hess,g,3); full=[int(np.linalg.matrix_rank(H,1e-8)) for H in Hc]
    Q,Fs,rk=setup(g); quot=[int(np.linalg.matrix_rank(F,1e-8)) for F in Fs]
    print('%-22s dimL %d rank(g) %d max|3x3 subperm| %.1e max|4x4| %.1e |perm| %.1e  gradrank %d  Hess ranks full %s  on U/g(dim %d) %s'%(name,V.shape[0],np.linalg.matrix_rank(g,1e-9),sub3(g),sub4(g),abs(np.linalg.det(g)) if False else abs(sum(np.prod([g[i,p[i]] for i in range(5)]) for p in itertools.permutations(range(5)))),rk,full,Q.shape[1],quot),flush=True)
