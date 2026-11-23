# Test of (*):  for M level containing e_i w^T, (X;rho) in T_1(M), Y in M:
#     perm[ pi_i(J+Y) ; w o rho ] = (<w,rho>/5) * perm[ pi_i(J+Y) ; 1 ]      (pi_i(J+Y) = the four rows != i of J+Y, incl. the ones row r)
import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/reg2'); sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
import numpy as np, glob
from t import *
from a1 import embed
from a5 import onb, rref_tol
from a6 import T1
rg=np.random.default_rng(0)
def Nvec(Z): return np.array([perm(np.delete(Z,j,axis=1)) for j in range(5)])
def test(B,label):
    B=onb(B); worst=0; worst2=0; n=0
    T=T1(embed(B),rg,npts=130)
    for i in range(4):
        SR=rowpart(B,[i])
        for el in SR:
            w=el[i]
            for _ in range(4):
                c=rg.normal(size=len(B))+1j*rg.normal(size=len(B)); Y=np.einsum('k,kab->ab',c,B)
                Z=np.ones((4,5),complex); rows=[k for k in range(4) if k!=i]; Z[:3]+=Y[rows]       # three rows + ones row
                Nz=Nvec(Z)
                for t in T:
                    rho=t[4]; lhs=((w*rho)*Nz).sum(); rhs=(w@rho)/5*Nz.sum()
                    worst=max(worst,abs(lhs-rhs)/(1e-12+np.abs(Nz).max()*np.abs(w).max()*np.abs(rho).max())); n+=1
    print('%-40s dim %d dim T1 %d: %d checks, max rel deviation %.1e'%(label,len(B),len(T),n,worst))
files=['Mstar2.npy','M_L080_col0.npy','../rows/rc45.npy','dr_u3_s1_1.npy','linespan_other_s2_41_0.npy']
for f in files:
    B=onb(np.load(f)); test(B,f.split('/')[-1])
    # sub-configurations containing a single-row element: span(e_i w^T, two random elements of M)
    for i in range(4):
        SR=rowpart(B,[i])
        if len(SR)==0: continue
        for trial in range(2):
            C=rg.normal(size=(2,len(B)))+1j*rg.normal(size=(2,len(B)))
            sub=np.concatenate([SR[:1],np.einsum('kc,cab->kab',C,B)],0); test(sub,'   sub: 1 single-row (row %d) + 2 random'%i)
        break
for f in ['nc_d6_k1_s23','nc_d6_k1_s4','seed_d6_e3_t4']:
    test(onb(rref_tol(onb(np.load('../rows/%s.npy'%f)),1e-5)),f)
