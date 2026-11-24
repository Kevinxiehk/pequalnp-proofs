import sys, itertools, numpy as np; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
from pairlib import nullspace, rank, perm
import t8_two_minimal as T8, r3_leaves as RL
np.set_printoptions(precision=3,suppress=True,linewidth=220)
def reps(s12,s13):
    w2,A1,A2=T8.struct(*s12); w3,B1,B3=T8.struct(*s13)
    out,cons,K,M0,R1=RL.leaves(s12,s13)
    R12=np.eye(15)[:10]@K; R13=np.vstack([np.eye(15)[:5],np.eye(15)[10:]])@K; r12=rank(R12); r13=rank(R13)
    one=np.ones(5); z=np.zeros(5)
    T=np.array([np.concatenate([one,z]),np.concatenate([z,one]),np.concatenate([A2,z]),np.concatenate([z,B3])])
    Tn=nullspace(T); res=[]
    for key in out:
        Nu=key[len(R1):]
        if rank(np.vstack([R12,Nu]))==r12 or rank(np.vstack([R13,Nu]))==r13: continue
        P=nullspace(key); Vm=nullspace((M0@P).T); C=Tn.conj().T@Vm; r=rank(C)
        u,s,vh=np.linalg.svd(C,full_matrices=False); res.append((Tn@u[:,:r]).T)
    return res
cfgs=[(('II',(0,0,0,1,2),1),('II',(0,0,1,0,2),1)),(('II',(0,0,0,1,2),1),('II',(0,1,1,0,2),1)),(('II',(0,0,1,1,2),1),('II',(1,1,0,0,2),1)),
      (('II',(0,0,1,1,2),1),('II',(0,1,0,0,2),1)),(('II',(0,1,2,2,2),1),('II',(0,1,2,2,2),-1))]
for s12,s13 in cfgs:
    print(s12[1:],s13[1:])
    for b in reps(s12,s13)[:5]:
        print('  admissible n** (dim %d) modulo trivial:'%len(b))
        for v in b:
            k=np.argmax(np.abs(v)); v=v/v[k]; print('     m_2 =',v[:5],' m_3 =',v[5:])
