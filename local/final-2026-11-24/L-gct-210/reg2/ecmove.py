# "EC moves" of Type F spaces: M_F = e_3 (x) 1^perp (+) N with N (2-dim, rows 0-2) having equal columns a,b;
#  M(a,b,i) := e_3 (x) {w : sum w = 0, w_a = w_b} (+) N (+) C e_i (e_a - e_b)^T  (level by rows' Lemma EC), no full free row if i != 3.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np, itertools
from t import *
from a1 import embed, defect, phirank
from a5 import onb
from a6 import T1, E0
from r5_FO2 import FO2
rg=np.random.default_rng(0)
def build(N,a,b,i):
    B=[]
    # basis of {w: sum w=0, w_a=w_b}
    A=np.array([np.ones(5),np.eye(5)[a]-np.eye(5)[b]]); u,s,vh=np.linalg.svd(A); 
    for w in vh[2:]:
        m=np.zeros((4,5),complex); m[3]=w; B.append(m)
    B+=list(N)
    m=np.zeros((4,5),complex); m[i,a]=1; m[i,b]=-1; B.append(m)
    return np.array(B)
def col(c,x):
    m=np.zeros((4,5),complex); m[:3,c]=x; return m
w=np.exp(2j*np.pi/3)
Ns={'single column 4: {x e_4^T}':[col(4,[1,-1,0]),col(4,[1,1,-2])],
    'x e_0^T, y e_3^T (M*)':[col(0,[1,-1,0]),col(3,[1,1,-2])],
    'rc45 plane u(e_0-e_1), ubar(e_2-e_3)':[col(0,[1,w,w*w])-col(1,[1,w,w*w]),col(2,[1,w*w,w])-col(3,[1,w*w,w])]}
for name,N in Ns.items():
    N=np.array(N); zero=[c for c in range(5) if np.abs(N[:,:,c]).max()<1e-12]
    eq=[(a,b) for a in range(5) for b in range(a+1,5) if np.abs(N[:,:,a]-N[:,:,b]).max()<1e-12]
    print('N =',name,' equal column pairs',eq)
    for (a,b) in eq:
        for i in (0,2):
            B=onb(build(N,a,b,i)); le=level_err(B,ntest=60)
            T=T1(embed(B),rg,npts=120); S=np.linalg.svd(T[:,4,:],compute_uv=False)
            fo=[FO2(embed(B),np.random.default_rng(k)) for k in range(2)]
            print('   (a,b)=(%d,%d) row i=%d: dim %d level err %.0e, e=%d, dim T1 %d, dim Omega %d, FO2 %s %s'%(a,b,i,len(B),le,int((defect(B)>1e-8).sum()),len(T),int((S>1e-8).sum()),fo[0],fo[1]))
            np.save('ec_%s_%d%d_%d.npy'%(name[:6].replace(' ','_'),a,b,i),B)
