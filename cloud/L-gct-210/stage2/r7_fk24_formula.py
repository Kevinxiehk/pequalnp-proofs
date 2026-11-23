# Check of the hand formulas for the cofactors of U = J + xi on the (2,4) ambient space (rows 0: ones; 1,2: 1 + s_k e_0; 3,4: 1 + p, 1 + q)
# and of the reduction used in R7-2:  C_0j - C_1j = s_1 gamma_j,  C_0j - C_2j = s_2 gamma_j,  C_00 = C_10 = C_20 = 2 gamma.
import itertools, numpy as np
P4=np.array(list(itertools.permutations(range(4))))
def cof(M,i,j):
    A=np.delete(np.delete(M,i,axis=0),j,axis=1); return A[np.arange(4)[None,:],P4].prod(axis=1).sum()
rg=np.random.default_rng(0); worst=0
for _ in range(20):
    s1,s2=rg.normal(size=2)+1j*rg.normal(size=2); p=rg.normal(size=5)+1j*rg.normal(size=5); q=rg.normal(size=5)+1j*rg.normal(size=5)
    U=np.ones((5,5),complex); U[1,0]+=s1; U[2,0]+=s2; U[3]+=p; U[4]+=q
    P0,Q0=1+p[0],1+q[0]; Pp,Qp=1+p[1:],1+q[1:]; al,be=Pp.sum(),Qp.sum(); gam=al*be-(Pp*Qp).sum(); s=s1+s2; A=3+s
    worst=max(worst,abs(cof(U,0,0)-2*gam),abs(cof(U,1,0)-2*gam),abs(cof(U,2,0)-2*gam),abs(cof(U,3,0)-6*be),abs(cof(U,4,0)-6*al))
    for j in range(1,5):
        aj=al-Pp[j-1]; bj=be-Qp[j-1]; gj=aj*bj-(Pp*Qp).sum()+Pp[j-1]*Qp[j-1]; h=2*P0*bj+2*Q0*aj
        worst=max(worst,abs(cof(U,0,j)-((2+s)*gj+h)),abs(cof(U,1,j)-((2+s2)*gj+h)),abs(cof(U,2,j)-((2+s1)*gj+h)),abs(cof(U,3,j)-(2*A*bj+6*Q0)),abs(cof(U,4,j)-(2*A*aj+6*P0)))
print('max deviation of the hand formulas for the 25 cofactors over 20 random points: %.1e'%worst)
