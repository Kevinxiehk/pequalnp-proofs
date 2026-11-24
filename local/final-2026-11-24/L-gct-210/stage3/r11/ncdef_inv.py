# invariants of (w2, w3) for the stored ncdef member vs random members
import sys, numpy as np
np.set_printoptions(precision=5,suppress=True,linewidth=160)
Z=np.load('/home/kevxhk/work/L-gct-210/rows/ncdef_d5_e2_k1_s1.npy'); d=len(Z)
def srow(r):
    A=np.array([[Z[k][i,j] for k in range(d)] for i in range(4) if i!=r for j in range(5)]); u,s,vh=np.linalg.svd(A); c=vh[-1].conj()
    w=np.tensordot(c,Z,axes=1)[r]; return w/w[4]
w2,w3=srow(2),srow(3)
print('w2 =',w2); print('w3 =',w3)
def inv(w2,w3):
    return {'<w2,w2>':w2@w2,'<w3,w3>':w3@w3,'<w2,w3>':w2@w3,'p3(w2)':(w2**3).sum(),'p3(w3)':(w3**3).sum(),'<w2^2,w3>':(w2*w2)@w3,'<w2,w3^2>':w2@(w3*w3),
            'p4(w2)':(w2**4).sum(),'p4(w3)':(w3**4).sum(),'<w2^2,w3^2>':(w2*w2)@(w3*w3),'<w2^3,w3>':(w2**3)@w3,'<w2,w3^3>':w2@(w3**3)}
for k,v in inv(w2,w3).items(): print('  %-12s %s'%(k,np.round(v,6)))
def rk(vs,tol=1e-6):
    s=np.linalg.svd(np.array(vs),compute_uv=False); return int((s>tol*s[0]).sum()), np.round(s/s[0],8)
o=np.ones(5); e0=np.eye(5)[0]
for name,vs in [('w2,w3,w2w3',[w2,w3,w2*w3]),('w2,w2w3',[w2,w2*w3]),('w3,w2w3',[w3,w2*w3]),('w2,w2w2,1,e0',[w2,w2*w2,o,e0]),
                ('w3,w3w3,1,e0',[w3,w3*w3,o,e0]),('w2,w3,1,e0,w2w3',[w2,w3,o,e0,w2*w3]),('w2,w3,1,e0,w2w2',[w2,w3,o,e0,w2*w2]),('w2,w3,1,e0,w3w3',[w3,w2,o,e0,w3*w3])]:
    print('%-18s rank %s'%(name,rk(vs)))
