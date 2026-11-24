import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np
from lib import level_poly
from clm import *
from seeded import defect_basis
rng=np.random.default_rng(0)
def e(i,n=4):
    v=np.zeros(n,complex); v[i]=1; return v
def fam(m,c,phi1=None,phi2=None,colA=2,colB=4):
    """4x5 space: e_2 m^T, (1,1,-3,1) e_4^T, (e0-e3) e_2^T + c phi1 e_4^T, (e1-e3) e_2^T + c phi2 e_4^T"""
    phi1=e(1)-e(2) if phi1 is None else phi1; phi2=e(1)-2*e(2)+e(3) if phi2 is None else phi2
    Z=np.zeros((4,4,5),complex)
    Z[0,2,:]=m
    Z[1,:,colB]=[1,1,-3,1]
    Z[2,:,colA]=e(0)-e(3); Z[2,:,colB]+=c*phi1
    Z[3,:,colA]=e(1)-e(3); Z[3,:,colB]+=c*phi2
    return Z
def test(Z,label):
    s=defect_dim(Z)
    print(label,'4x5 level err %.1e'%fresh_level(Z),'defect sv',np.array2string(s[:4],precision=2))
Zs=np.load('clm_p4_d4_defect1_s8.npy')
m=defect_basis(Zs,1)[0]; m=m/m[0]; c=0.7829-2.5268j
print('m',m,'sum',m.sum(),'m.m',(m*m).sum(),'sum m^3',(m**3).sum())
test(fam(m,c),'numeric m,c')
for cc in (1.0,2.0-1j,0.3j): test(fam(m,cc),'same m, c=%s'%cc)
m2=rng.normal(size=5)+1j*rng.normal(size=5); m2[4]=0; m2[:4]-=m2[:4].mean()
test(fam(m2,c),'random m (m_4=0), same c')
m3=np.array([1,2,-4,1,0],complex); test(fam(m3,1.0),'m=(1,2,-4,1,0), c=1')
# relations?
print('m_2',m[2],'c',c,'c*m_2',c*m[2],'c^2',c*c, 'c^2*m2',c*c*m[2], '(1+m2)',1+m[2])
