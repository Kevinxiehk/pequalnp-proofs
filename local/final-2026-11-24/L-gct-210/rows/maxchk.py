import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/numerics')
import numpy as np, glob
from build7 import build, check
from core import ext_space, fresh_check, Pk
tot=0; bad=0; types={}
for pat in ('clm_p4_d4_defect1_s*.npy','seed_d4_e1_t*.npy','clm_p4_d5_defect2_s*.npy','seed_d5_e2_t*.npy','clm_p4_d6_defect3_s*.npy','seed_d6_e3_t*.npy','clm_p4_d3_defect0_s*.npy'):
    for f in sorted(glob.glob(pat)):
        Z=np.load(f); B,e=build(Z); dim=np.linalg.matrix_rank(B.reshape(len(B),-1)); dE,E,s=ext_space(B)
        # extra direction: component of E orthogonal to L ; its P_2
        Q=np.linalg.qr(B.reshape(len(B),-1).T)[0]; Em=E.reshape(dE,-1)
        R=Em-(Em@Q.conj())@Q.T; u,sv,vh=np.linalg.svd(R); y=vh[0].reshape(5,5)
        yr=np.zeros((5,5)); yr[4]=1; yr-=0.2
        cosang=abs(np.vdot(yr.ravel(),y.ravel()))/np.linalg.norm(yr)
        p2=abs(Pk(y[None])[0,2])
        tot+=1; key=(len(Z),e); types[key]=types.get(key,0)+1
        ok=(dim==7 and dE==8 and cosang>1-1e-6 and fresh_check(B)<1e-9)
        if not ok: bad+=1; print('EXCEPTION',f,dim,dE,cosang,fresh_check(B),s[24-dE],s[25-dE])
print('checked',tot,'spaces; types (dim L\',e):count',types,'; exceptions',bad,'(ok = dim 7, level, dim E = 8, extra first-order direction = e_r 1^T - J/5)')
