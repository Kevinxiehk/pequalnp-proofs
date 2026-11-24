import sys; sys.path.insert(0,"/home/kevxhk/work/L-gct-210/numerics/r2")
from spaces import *
rng=np.random.default_rng(3)
B={'ex1':ex1(),'fam':fam(0.3+0.7j),'L080':L080()}[sys.argv[1]]
dE,E,_=ext_space(B)
sB=E+0.05*(rng.normal(size=E.shape)+1j*rng.normal(size=E.shape))
fc,Bn=lm_space(sB,8,ambient=sumzero_ambient(),iters=600,tlimit=float(sys.argv[2]),rng=rng,rounds=8,verbose=True)
np.save(f'long8_{sys.argv[1]}.npy',Bn)
Q=orth(Bn); print('final fresh',fc,'invariants',invariants(Bn),'sv of basis ok')
# how far is the 8-dim stall space from containing a 7-dim level space? angle to seed L
print('sin angle between L and stall space (L in it?):', angle(B,Bn[:0].reshape(0,5,5)) if False else np.linalg.svd(orth(B).reshape(7,-1).conj()@Q.reshape(8,-1).T,compute_uv=False).min())
