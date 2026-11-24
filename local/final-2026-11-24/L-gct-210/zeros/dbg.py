import numpy as np, itertools, sys
sys.path.insert(0,'/home/kevxhk/work/L-gct-086/smallcases'); import level
w=np.exp(2j*np.pi/3)
def E(v,j):
    t=np.zeros((4,5),complex); t[:,j]=v; return t.ravel()
z=np.array([1,w,w*w,0]); h=np.array([1,1,1,-3])
for nm,F in [('II',[E(z,0)-E(z,1),E(z.conj(),2)-E(z.conj(),3)]),('II+h e4',[E(z,0)-E(z,1),E(z.conj(),2)-E(z.conj(),3),E(h,4)])]:
    F=np.array(F); rng=np.random.default_rng(0); S=rng.normal(size=(20,len(F)))+1j*rng.normal(size=(20,len(F)))
    Y=(S@F).reshape(-1,4,5); print(nm,[float(np.round(abs(level.Pk(np.delete(Y,j,axis=2)))[:,1:].max(),10)) for j in range(5)])
