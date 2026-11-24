# Round 11, target 1: for a 3-dim W inside 1^perp and a NON-constant zeta, the linear space of B: W -> 1^perp with
#   b(w,w') = <w,Bw'> skew  and  beta_zeta(w,w') = sum_c zeta_c w_c (Bw')_c skew  (SK2);  report its dimension and the generic rank of B.
import numpy as np, itertools
rg=np.random.default_rng(7)
F=np.array([[1 if c==i else (-1 if c==4 else 0) for c in range(5)] for i in range(4)],float)   # basis of 1^perp
def analyse(Wb,zeta):
    # unknown B: B w_i = sum_k c[i,k] F_k  (12 unknowns)
    rows=[]
    for i in range(3):
        for l in range(i,3):
            for z in (np.ones(5),zeta):
                row=np.zeros((3,4),complex)
                # sym part: <w_i o z, B w_l> + <w_l o z, B w_i>
                for k in range(4):
                    row[l,k]+=np.sum(Wb[i]*z*F[k]); row[i,k]+=np.sum(Wb[l]*z*F[k])
                rows.append(row.ravel())
    A=np.array(rows); u,s,vh=np.linalg.svd(A); r=int((s>1e-9*s[0]).sum()); N=vh[r:].conj()
    if len(N)==0: return 0,0
    c=(rg.normal(size=len(N))+1j*rg.normal(size=len(N)))@N
    Bimg=c.reshape(3,4)@F
    return len(N),np.linalg.matrix_rank(Bimg,tol=1e-8)
for wtype in ('random W','W containing an isotropic n'):
    print('==',wtype)
    for zt,zeta in [('(4,1)',np.array([1,1,1,1,0.])),('(3,2)',np.array([1,1,1,0,0.])),('(3,1,1)',np.array([1,1,1,0,2.])),('(2,2,1)',np.array([1,1,0,0,2.])),('(2,1,1,1)',np.array([1,1,0,2,3.])),('5 distinct',np.array([0,1,2,3,5.]))]:
        res=[]
        for t in range(3):
            if wtype=='random W':
                n=F.T@(rg.normal(size=4)+1j*rg.normal(size=4))
            else:
                # isotropic n in 1^perp: n = (1,w,w^2,0,0) permuted randomly
                w=np.exp(2j*np.pi/3); n=np.array([1,w,w*w,0,0]); n=n[rg.permutation(5)]
            A=np.array([np.ones(5),n]); u,s,vh=np.linalg.svd(A); Wb=vh[2:].conj()     # W = {1,n}^perp (bilinear: use conj of null of A)
            Wb=np.linalg.svd(np.array([np.ones(5),n]))[2][2:].conj()
            # check bilinear orthogonality
            assert np.abs(Wb@np.ones(5)).max()<1e-9 and np.abs(Wb@n).max()<1e-9
            P=rg.permutation(5); res.append(analyse(Wb,zeta[P]))
        print('  zeta type %-10s: (dim of B-space, generic rank B) = %s'%(zt,res))
