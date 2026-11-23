# FILTER for regime 1 (rows with a_r = 1): L_r must be a 5-dim level 4x5 space with Phi = 0 and Omega(L_r) = C^5.
# Test: hyperplanes of Type F spaces with Omega = C^5 and of M*-type spaces.
import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/reg2'); sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
import numpy as np
from t import *
from a1 import embed, defect, phirank
from a5 import onb
from a6 import T1, E0
from r5_FO2 import FO2
E=np.eye(5)
def rowel(i,v):
    m=np.zeros((4,5),complex); m[i]=v; return m
def col(c,x):
    m=np.zeros((4,5),complex); m[:3,c]=x; return m
free=[rowel(3,E[j]-E[4]) for j in range(4)]
U12=[rowel(3,[2,-1,-1,0,0]),rowel(3,[0,-1,-1,2,0]),rowel(3,[0,-1,-1,0,2])]
EC=rowel(2,E[1]-E[2])
spaces={'F1 = free row + {x e_4}':free+[col(4,[1,-1,0]),col(4,[1,1,-2])],
        'F2 = free row + x e_0, y e_3':free+[col(0,[1,-1,0]),col(3,[1,1,-2])],
        'M*_1':U12+[col(0,[1,-1,0]),col(3,[1,1,-2]),EC],
        'M*_2':U12+[col(4,[1,-1,0]),col(4,[1,1,-2]),EC]}
rg=np.random.default_rng(1)
def inv(B):
    B=onb(B); T=T1(embed(B),rg,npts=140); S=np.linalg.svd(T[:,4,:],compute_uv=False)
    sr=[len(rowpart(B,[i])) for i in range(4)]
    return 'srow %s e=%d PhiRk=%d dimT1=%d dimOmega=%d FO2=%s'%(sr,int((defect(B)>1e-8).sum()),int((phirank(B)>1e-8).sum()),len(T),int((S>1e-8).sum()),FO2(embed(B),rg,npts=140))
for name,B in spaces.items():
    B=np.array(B); print(name,': full space:',inv(B))
    # generic hyperplane
    for k in range(2):
        C=rg.normal(size=(5,6))+1j*rg.normal(size=(5,6)); print('    generic hyperplane        :',inv(np.einsum('kc,cab->kab',C,B)))
    # special hyperplanes: drop one basis vector
    for k in range(6):
        idx=[j for j in range(6) if j!=k]; print('    drop basis vector %d       :'%k,inv(B[idx]))
