import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/hessmix')
from hk import *
ex=examples()
for k,B in ex.items():
    print(k, inv(B), 'res %.1e'%resid(B))
# check Q formula: 2P2 = -20|al|^2-20|be|^2+|g|^2 ; Q(t,t)=2P2
rng=np.random.default_rng(0)
t=rng.normal(size=(5,5)); t-=t.mean()
m,al,be,g=parts(t)
print(t.ravel()@Q25@t.ravel(), -20*(al@al)-20*(be@be)+(g*g).sum(), 2*Pk(t)[0,2])
