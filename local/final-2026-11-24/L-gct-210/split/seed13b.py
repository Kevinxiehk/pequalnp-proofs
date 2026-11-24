import sys; sys.path.insert(0,'.')
from seed13 import *
rng=np.random.default_rng(int(sys.argv[1]))
L=np.load(sys.argv[2]); Lf=L.reshape(len(L),-1); Q,_=np.linalg.qr(Lf.T); O=Q.T.reshape(len(L),5,5)
D=rde(L,1e-6)['D'][0]
c=rnd((2,len(L)),rng); S=np.concatenate([D[None],np.einsum('qk,kij->qij',c,O)])
E=ext_space(S); C=complement(S,E); print('L3',info(S),'E',len(E),'C',len(C))
sols=[]
import time; t0=time.time()
for s in range(40):
    f,L4,_=search(S,1,starts=1,seed=1000*s+int(sys.argv[1]),tlimit=15,C=C)
    if f<1e-10:
        I=info(L4,1e-6); 
        # principal angle of new vector vs ex2 span
        x=L4[3].reshape(-1); y=x-Q@(Q.conj().T@x); inside=np.linalg.norm(y)/np.linalg.norm(x)
        sols.append((I['rA'],I['rB'],I['d'],round(inside,6)))
        print(' sol res %.1e fresh %.1e'%(f,fresh(L4)),I,'dist from ex2 span %.2e'%inside,flush=True)
    else: print(' start',s,'res %.1e'%f,flush=True)
    if time.time()-t0>float(sys.argv[3]): break
print('summary',sols)
