# Lemma check: Y_A = C^5_0 (x) w, w=(1/3)(-1,1,1,1,1) fixed; search Y_B (dim m, C onto an m-dim subspace) with QAB,QBB,TABB.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/hessmix')
import numpy as np
from scipy.optimize import least_squares
m=int(sys.argv[1]); rng=np.random.default_rng(int(sys.argv[2]))
w=np.array([-1,1,1,1,1])/3.
E4=np.array([np.eye(5)[k]-np.eye(5)[4] for k in range(4)])
YA=np.array([np.outer(E4[k],w).ravel() for k in range(4)])
def build(x):
    z=x[:len(x)//2]+1j*x[len(x)//2:]
    X=z[:m*25].reshape(m,5,5); X=X-X.mean(2,keepdims=True)   # row sums zero
    C=X.sum(1)                                                 # column sums (m x 5)
    return X.reshape(m,25),C
def res(x):
    Y,C=build(x)
    e=[(YA@Y.T).ravel(), (Y@Y.T-(5/9)*(C@C.T))[np.triu_indices(m)]]
    for a in YA: e.append(((Y*a)@Y.T)[np.triu_indices(m)])
    # normalisation: C restricted to first m coords of E4-chart = identity (C onto an m-dim space, fixed chart)
    Cc=np.linalg.lstsq(E4.T,C.T,rcond=None)[0].T  # m x 4 coordinates
    e.append((Cc[:, :m]-np.eye(m)).ravel())
    o=np.concatenate(e); o=np.concatenate([o.real,o.imag]); return np.concatenate([o,np.zeros(max(0,len(x)-len(o)))])
out=[]
for st in range(4):
    r=least_squares(res,rng.normal(size=2*m*25),method='lm',max_nfev=3000,xtol=1e-15,ftol=1e-15,gtol=1e-15)
    out.append(np.linalg.norm(r.fun))
print('m=%d'%m,'residuals',' '.join('%.1e'%v for v in out))
