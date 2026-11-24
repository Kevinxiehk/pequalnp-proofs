import sys, numpy as np
sys.path.insert(0, '/home/kevxhk/work/L-gct-086/smallcases')
from level import Pk
def rank(M, tol=1e-8):
    s = np.linalg.svd(M, compute_uv=False); return int((s > tol * s[0]).sum()), s
def RC():
    out=[]
    for i in range(5):
        T=np.zeros((5,5)); T[i,:]=1; out.append(T.ravel())
    for j in range(5):
        T=np.zeros((5,5)); T[:,j]=1; out.append(T.ravel())
    return np.array(out)
def analyse(Tb):
    d=len(Tb); K=Tb.reshape(d,25)
    K = np.linalg.qr(K.T)[0].T
    KK=[K[a]*K[b] for a in range(d) for b in range(a,d)]
    X=np.vstack([np.ones((1,25)), K, np.array(KK)])
    rX,_=rank(X); rRC,_=rank(RC()); rZ,_=rank(np.vstack([X,RC()]))
    print('d',d,'dimX',rX,'dimRC',rRC,'dim(X+RC)',rZ,'dim X∩RC',rX+rRC-rZ, ' bound d<=25-dim(X+RC)=',25-rZ)
    # check conditions
    print(' p2 gram max', np.abs(K@K.T).max(), ' p3 max', np.abs(np.einsum('ai,bi,ci->abc',K,K,K)).max())
if __name__=='__main__':
    for f in sys.argv[1:]:
        print(f); analyse(np.load(f))

def quartics(Tb, trials=5, seed=0):
    rng=np.random.default_rng(seed); d=len(Tb)
    for _ in range(trials):
        x=rng.normal(size=d)+1j*rng.normal(size=d); x/=np.linalg.norm(x)
        t=np.einsum('i,iab->ab',x,Tb/np.abs(Tb).max())
        p4=(t**4).sum(); r=(t**2).sum(1); c=(t**2).sum(0); g=t@t.T
        tr=np.trace(g@g); P4=1.5*p4-0.75*((r**2).sum()+(c**2).sum())+0.125*(t**2).sum()**2+0.25*tr
        print(' p4 %.2e  sum r^2 %.2e sum c^2 %.2e tr %.2e  P4formula %.2e P4true %.2e rank t %d'%(abs(p4),abs((r**2).sum()),abs((c**2).sum()),abs(tr),abs(P4),abs(Pk(t)[0][4]), np.linalg.matrix_rank(t,1e-8)))
