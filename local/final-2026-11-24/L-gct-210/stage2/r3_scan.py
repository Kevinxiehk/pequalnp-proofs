# Conjugate exception family: scan the only free parameter delta of n** over a grid and report the minimal normalised cube
# defect on a transversal S; also check the hand formula perm_3 = const * c_1 * ell^2 at delta_h = 0 (delta = -i).
import sys, itertools, numpy as np; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import r3_survey as RS, r3_cube2 as RC, r3_hand_check as HC
from pairlib import nullspace
one=np.ones(5)
for comp in ((1,1,3),(1,3,1),(3,1,1),(1,2,2),(2,1,2),(2,2,1)):
    cells=np.array([0]*comp[0]+[1]*comp[1]+[2]*comp[2]); s12=(tuple(cells),1); s13=(tuple(cells),-1)
    w2,A1,A2,y12=RS.typeII(*s12); w3,B1v,B3,y13=RS.typeII(*s13); F=HC.F
    A0=np.array([F([(0,one),(1,-one)]),F([(0,one),(2,-one)]),F([(0,A1+y12*one),(1,A2)]),F([(0,B1v+y13*one),(2,B3)])]); u=np.array([one,1/w2,1/w3])
    q1=(cells==0).astype(float); q2=(cells==1).astype(float)
    S=(int(np.where(cells==0)[0][0]),int(np.where(cells==1)[0][0]),int(np.where(cells==2)[0][0]))
    mn=9
    for re in np.linspace(-4,4,33):
        for im in np.linspace(-4,4,33):
            n=F([(1,q1+(1-1j)*q2-(re+1j*im)*one),(2,-1j*q1)]); d,B1,defect,vs,ell,pm=HC.cube_test(A0,n,u,S)
            if B1: mn=min(mn,defect)
    n=F([(1,q1+(1-1j)*q2+1j*one),(2,-1j*q1)]); d,B1,defect,vs,ell,pm=HC.cube_test(A0,n,u,S)
    c1=np.array([v[2] for v in vs]); ratio=pm/(c1*ell**2)
    print(tuple(int(c) for c in cells),' min cube defect over the delta-grid: %.2f ;  at delta_h = 0: perm/(c_1 ell^2) ='%mn,np.round(ratio[:3],6),' defect %.2f'%defect)
