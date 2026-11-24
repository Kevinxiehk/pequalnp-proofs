import numpy as np, sys; sys.path.insert(0,"/home/kevxhk/work/L-gct-210/lemmaz")
from core import *
np.set_printoptions(precision=2,suppress=False,linewidth=220)
rng=np.random.default_rng(4); e1=np.eye(5)[0]
v=rng.normal(size=5)+1j*rng.normal(size=5)   # consume same random numbers as sing.py
def cof(g):
    out=np.zeros((5,5),complex)
    for i in range(5):
        for j in range(5):
            out[i,j]=(-1)**(i+j)*np.linalg.det(np.delete(np.delete(g,i,0),j,1))
    return out
want=[3,4,5,16,17,22]
for st in range(23):
    lam=rng.normal(size=25)+1j*rng.normal(size=25)
    x0=rng.normal(size=25)+1j*rng.normal(size=25)
    if st not in want: continue
    F=lambda x: np.concatenate([minors(x.reshape(5,5)).ravel(),[np.linalg.det(x.reshape(5,5)),lam@x-1]])
    x,r=solve(F,x0,nfev=20000)
    g=x.reshape(5,5); g=g/np.abs(g).max()
    sv=np.linalg.svd(g,compute_uv=False)
    U,S,Vh=np.linalg.svd(g); xl=U[:,-1].conj(); yr=Vh[-1].conj()
    print("run",st,"res %.1e"%r,"sv",sv)
    print("  |g|:\n",np.abs(g))
    print("  left kernel |x|",np.abs(xl)," right kernel |y|",np.abs(yr))
    print("  max|minor perms| %.1e  |det| %.1e"%(np.abs(minors(g)).max(),abs(np.linalg.det(g))))
    np.save("sing_run%d.npy"%st,g)
