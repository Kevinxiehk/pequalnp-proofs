import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2')
import numpy as np
from t import *
np.set_printoptions(precision=3,suppress=True,linewidth=200)
def rref(B):
    d=len(B); sh=B.shape[1:]; A=B.reshape(d,-1).astype(complex).copy(); piv=[]
    r=0
    for _ in range(d):
        # complete pivot among remaining rows: choose column maximizing the max abs
        sub=np.abs(A[r:]); i,j=np.unravel_index(np.argmax(sub),sub.shape); i+=r
        if abs(A[i,j])<1e-9: break
        A[[r,i]]=A[[i,r]]; A[r]/=A[r,j]
        for k in range(d):
            if k!=r: A[k]-=A[k,j]*A[r]
        piv.append(j); r+=1
    A[np.abs(A)<1e-7]=0
    return A[:r].reshape((r,)+sh),piv
def sparse_basis(B):
    """greedy: single-row parts, single-col parts, two-row parts ... then rref of the rest"""
    return rref(B)
if __name__=='__main__':
  for f in sys.argv[1:]:
    B=np.load(f); R,piv=rref(B)
    print('=====',f)
    for m in R:
        print(np.array2string(m,precision=3,suppress_small=True)); print()
