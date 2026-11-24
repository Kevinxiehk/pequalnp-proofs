# FO / FO2 of sub-configurations of M* (independent of x, y): which small piece already forces dim <= 8 ?
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from t import *
from a1 import embed
from a5 import onb
from a6 import T1
from r5_FO2 import FO2
E=np.eye(5)
def rowel(i,v):
    m=np.zeros((4,5),complex); m[i]=v; return m
def col(c,x):
    m=np.zeros((4,5),complex); m[:3,c]=x; return m
U12=[rowel(3,[2,-1,-1,0,0]),rowel(3,[0,-1,-1,2,0]),rowel(3,[0,-1,-1,0,2])]
EC=rowel(2,E[1]-E[2])
cfgs={'e_3(x)U (U={w1=w2})':U12,
      'split pair e_3(x)U + e_2(e1-e2)':U12+[EC],
      'split pair + x e_0 (x=(1,-1,0))':U12+[EC,col(0,[1,-1,0])],
      'split pair + x e_4 (x=(1,-1,0))':U12+[EC,col(4,[1,-1,0])],
      'split pair + x e_4 (x=(1,1,-2))':U12+[EC,col(4,[1,1,-2])],
      'e_3(x)U + {x e_4} (5-dim, no EC)':U12+[col(4,[1,-1,0]),col(4,[1,1,-2])],
      'full free row e_3(x)1^perp':U12+[rowel(3,E[1]-E[2])],
      'full free row + e_2(e1-e2) [not level?]':U12+[rowel(3,E[1]-E[2]),EC]}
for name,B in cfgs.items():
    B=onb(np.array(B)); le=level_err(B,ntest=40)
    if le>1e-9: print('%-42s NOT level'%name); continue
    T=T1(embed(B),np.random.default_rng(0),npts=140); S=np.linalg.svd(T[:,4,:],compute_uv=False)
    fo=[FO2(embed(B),np.random.default_rng(k),npts=140) for k in range(3)]
    print('%-42s dim %d: dim T1 %d dim Omega %d FO2 %s'%(name,len(B),len(T),int((S>1e-8).sum()),fo))
