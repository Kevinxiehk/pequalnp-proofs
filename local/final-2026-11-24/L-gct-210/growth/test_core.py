import numpy as np, sys
sys.path.insert(0,'.')
from core import *
rng=np.random.default_rng(1)
# verify Q,T proportional to polar forms of P2,P3 via level.Pk on t
t=rng.normal(size=(1,25))+1j*rng.normal(size=(1,25)); t=t-t.mean()
P=level.Pk(t.reshape(1,5,5))[0]
u=Phi(t)
print('2P2',2*P[2],'Q',Qf(u,u)[0])
print('P3',P[3],'(2/3)T',(2/3)*Tf(u,u,u)[0])
# check prod: Q(u∘v,w)=T(u,v,w)
a,b,c=[Phi((lambda x:x-x.mean())(rng.normal(size=(1,25))+1j*rng.normal(size=(1,25)))) for _ in range(3)]
p=prod(a,b); print('sum p',p.sum(), 'Q(p,c)',Qf(p,c)[0],'T',Tf(a,b,c)[0])
L=rand_iso(9,rng); print('iso check',checkP23(L)[0]); print('growth random iso 9',growth(L))
for l in [3,4,5,6,7,8,9,10,11,12]:
    L=rand_iso(l,rng); print(l,growth(L))
