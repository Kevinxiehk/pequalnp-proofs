# verify2: follow-up on the free-b search for N3': inspect near-solutions (are they bounded or blow-ups towards perm(b)=0 ?)
import numpy as np, sys, time
sys.path.insert(0,'/home/claude/work/L-gct-210/verify2')
import n3p_search as N
from scipy.optimize import least_squares
rng=np.random.default_rng(int(sys.argv[1])); N.rng=rng
k=4; X=rng.normal(size=(60,k))+1j*rng.normal(size=(60,k)); t0=time.time(); rec=[]
while time.time()-t0<float(sys.argv[2]):
    piv=sorted(rng.choice(9,size=k,replace=False)); oth=[c for c in range(9) if c not in piv]; nF=k*(9-k); n=nF+9
    def unpack(z):
        zc=z[:n]+1j*z[n:]; F=zc[:nF].reshape(k,9-k); V=np.zeros((k,9),complex); V[:,piv]=np.eye(k); V[:,oth]=F; return V,zc[nF:]
    def res(z):
        V,bb=unpack(z); r=N.perm3(bb[None,:]+X@V)-N.perm3(bb); r=np.concatenate([r,[N.perm3(bb)-1]]); return np.concatenate([r.real,r.imag])
    z0=rng.normal(size=2*n)*rng.choice([0.3,1.0,2.0])
    b0=N.STRUCT[rng.integers(len(N.STRUCT))].reshape(9)+0.3*(rng.normal(size=9)+1j*rng.normal(size=9)); z0[nF:n]=b0.real; z0[n+nF:]=b0.imag
    sol=least_squares(res,z0,method='lm',max_nfev=3000)
    V,bb=unpack(sol.x); rec.append((np.linalg.norm(sol.fun),np.abs(V).max(),np.abs(bb).max(),sol.nfev,V,bb))
rec.sort(key=lambda t:t[0])
print('starts',len(rec))
for r in rec[:6]: print('res %.2e  max|V| %.2e  max|b| %.2e  nfev %d'%r[:4])
r=rec[0]; np.set_printoptions(precision=3,suppress=True,linewidth=200)
print('best: b =\n',r[5].reshape(3,3)); print('V =\n',r[4])
