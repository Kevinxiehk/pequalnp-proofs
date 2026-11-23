import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/reg2')
import numpy as np
from t import *
def onb(B):
    d=len(B); sh=B.shape[1:]; u,s,vh=np.linalg.svd(B.reshape(d,-1),full_matrices=False); r=int((s>1e-8*s[0]).sum()); return vh[:r].reshape((r,)+sh)
for f in sys.argv[1:]:
    B=onb(np.load(f)); d=len(B)
    out=[]
    for i in range(4):
        m=np.zeros((4,5),bool); m[i]=True
        A=B.reshape(d,-1)[:,~m.ravel()].T; out.append(np.linalg.svd(A,compute_uv=False))
    print(f.split('/')[-1]); 
    for i in range(4): print('   row',i,'sv of complement-restriction',np.array2string(out[i],precision=2))
