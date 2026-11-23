import sys, itertools, numpy as np; sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
from pairlib import nullspace, rank, perm
import t8_two_minimal as T8, r3_leaves as RL
np.set_printoptions(precision=3,suppress=True,linewidth=200)
def reps(s12,s13):
    w2,A1,A2=T8.struct(*s12); w3,B1,B3=T8.struct(*s13)
    out,cons,K,M0,R1=RL.leaves(s12,s13)
    one=np.ones(5); z=np.zeros(5)
    T=np.array([np.concatenate([one,z]),np.concatenate([z,one]),np.concatenate([A2,z]),np.concatenate([z,B3])])  # trivial rows-2,3 functionals
    Tn=nullspace(T)             # complement basis (10 x 6), orthonormal
    res=[]
    for key in out:
        # recover m-space: all m in C^10 with (m@M0) in rowspace(key)
        P=nullspace(key)        # vectors orthogonal to rowspace(key)  (9 x k)
        A=(M0@P).T              # m@M0@P = 0
        Vm=nullspace(A)         # 10 x d
        # reduce mod T: project onto complement
        C=Tn.conj().T@Vm; r=rank(C)
        u,s,vh=np.linalg.svd(C,full_matrices=False); basis=(Tn@u[:,:r]).T
        res.append(basis)
    return res
for s12,s13 in [(('II',(0,1,1,1,2),1),('II',(0,1,1,1,2),-1)),(('II',(0,1,1,2,2),1),('II',(0,1,1,2,2),-1)),(('II',(0,0,1,1,2),1),('II',(0,0,1,1,2),-1)),
                (('II',(0,1,1,1,2),1),('II',(1,0,0,0,2),1))]:
    print(s12[1:],s13[1:])
    for b in reps(s12,s13)[:4]:
        print('  solution space (dim %d) of (m_2 | m_3) modulo trivial:'%len(b))
        for v in b:
            k=np.argmax(np.abs(v)); v=v/v[k]; print('     m_2 =',v[:5],' m_3 =',v[5:])
