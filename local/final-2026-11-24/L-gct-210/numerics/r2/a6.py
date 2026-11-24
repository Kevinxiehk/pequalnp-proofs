import sys; sys.path.insert(0,"/home/kevxhk/work/L-gct-210/numerics/r2")
from spaces import *
np.set_printoptions(precision=3,suppress=True,linewidth=200)
def rref(B,tol=1e-6):
    M=orth(B).reshape(len(B),-1).copy(); r=0; piv=[]
    for c in range(25):
        if r==len(M): break
        p=r+np.argmax(abs(M[r:,c]))
        if abs(M[p,c])<tol: continue
        M[[r,p]]=M[[p,r]]; M[r]/=M[r,c]
        for k in range(len(M)):
            if k!=r: M[k]-=M[k,c]*M[r]
        piv.append(c); r+=1
    return M.reshape(-1,5,5),piv
if __name__=="__main__":
  s0=np.load('sol7_ex1_d0_0.npy')
  R,piv=rref(s0); print('pivots',piv)
  for m in R: print(np.round(m,4)); print()
  print('S = ex1 drop B1, basis:'); 
