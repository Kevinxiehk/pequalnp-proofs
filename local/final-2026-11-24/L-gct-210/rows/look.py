import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np
from clm import *
from seeded import defect_basis
np.set_printoptions(precision=4,suppress=True,linewidth=200)
def rref(M,tol=1e-8):
    M=M.copy(); r=0; piv=[]
    for c in range(M.shape[1]):
        if r==M.shape[0]: break
        k=r+np.argmax(np.abs(M[r:,c]))
        if abs(M[k,c])<tol: continue
        M[[r,k]]=M[[k,r]]; M[r]/=M[r,c]
        for i in range(M.shape[0]):
            if i!=r: M[i]-=M[i,c]*M[r]
        piv.append(c); r+=1
    M[np.abs(M)<1e-9]=0
    return M,piv
f=sys.argv[1]; Z=np.load(f); d=len(Z)
e=int(sys.argv[2]); E=defect_basis(Z,e)
Er,_=rref(E.copy()); print('defect space (rref):'); print(Er)
order=[int(x) for x in sys.argv[3].split(',')] if len(sys.argv)>3 else list(range(20))
M,piv=rref(Z.reshape(d,20)[:,order])
inv=np.argsort(order)
print('pivots (cells)',[divmod(order[p],5) for p in piv])
for k in range(d):
    print(M[k][inv].reshape(4,5)); print()
