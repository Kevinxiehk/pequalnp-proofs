# For each of the 12 configurations surviving r3_survey.py: random admissible n** (random element of each leaf + random
# multiple of f_2); report the worst cube defect over all column triples S with ell != 0 on Pi_S  (1 = far from a cube).
import sys, itertools, numpy as np; sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
from pairlib import nullspace, rank
import r3_cube2 as RC, r3_hand_check as HC
rng=np.random.default_rng(9)
def rnd(*k): return rng.normal(size=k)+1j*rng.normal(size=k)
surv=[(((0,1,2,2,2),1),((0,1,2,2,2),-1)),(((0,1,1,1,2),1),((0,1,1,1,2),-1)),(((0,0,0,1,2),1),((0,0,0,1,2),-1)),
      (((0,0,0,1,2),1),((0,1,1,0,2),1)),(((0,0,0,1,2),1),((1,0,1,0,2),1)),(((0,0,0,1,2),1),((1,1,0,0,2),1)),
      (((0,1,1,2,2),1),((0,1,1,2,2),-1)),(((0,0,1,2,2),1),((0,0,1,2,2),-1)),(((0,0,1,1,2),1),((0,0,1,1,2),-1)),
      (((0,0,1,1,2),1),((0,1,0,0,2),1)),(((0,0,1,1,2),1),((1,0,0,0,2),1)),(((0,0,1,1,2),1),((1,1,0,0,2),1))]
f2=np.concatenate([np.ones(5),np.zeros(5)])
for s12,s13 in surv:
    A0,u,sols,triv=RC.leaves(s12,s13); rec=[]
    for V in sols:
        worst=[]
        for t in range(5):
            m=V@rnd(V.shape[1])+rnd(1)[0]*f2; n=np.concatenate([np.zeros(5),m]); mx=0; cnt=0
            for S in itertools.combinations(range(5),3):
                d,B1,defect,vs,ell,pm=HC.cube_test(A0,n,u,S)
                if B1: cnt+=1; mx=max(mx,defect)
            worst.append(round(mx,2))
        rec.append((V.shape[1],cnt,min(worst)))
    print(s12,s13,' leaves:',len(sols),' (dim, #S with ell!=0, min over 5 random n** of the worst cube defect):',rec)
