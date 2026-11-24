# verify2: independent counterexample search for N3' (4-dim lineality space of perm_3 at b, perm(b) != 0).
# Formulation: chart V_0 = rowspace[ I_k | F ] on a random choice of k pivot cells; residuals = perm(b + sum x_i v_i) - perm(b) at fixed
# random complex sample points (a cubic in <= 4 variables vanishing at 60 generic points vanishes identically).
import numpy as np, itertools, sys, time
from scipy.optimize import least_squares
rng=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0)
def perm3(A):
    a=A.reshape(A.shape[:-1]+(3,3))
    return (a[...,0,0]*(a[...,1,1]*a[...,2,2]+a[...,1,2]*a[...,2,1])+a[...,0,1]*(a[...,1,0]*a[...,2,2]+a[...,1,2]*a[...,2,0])
           +a[...,0,2]*(a[...,1,0]*a[...,2,1]+a[...,1,1]*a[...,2,0]))
def run(b,k,nstart,freeb=False,tmax=40):
    t0=time.time(); found=0; best=1e9; sols=[]
    X=rng.normal(size=(60,k))+1j*rng.normal(size=(60,k))
    for s in range(nstart):
        if time.time()-t0>tmax: break
        piv=sorted(rng.choice(9,size=k,replace=False)); oth=[c for c in range(9) if c not in piv]
        nF=k*(9-k)
        def unpack(z):
            zc=z[:len(z)//2]+1j*z[len(z)//2:]
            F=zc[:nF].reshape(k,9-k); V=np.zeros((k,9),complex); V[:,piv]=np.eye(k); V[:,oth]=F
            bb=zc[nF:nF+9] if freeb else b.reshape(9)
            return V,bb
        def res(z):
            V,bb=unpack(z)
            r=perm3(bb[None,:]+X@V)-perm3(bb)
            if freeb: r=np.concatenate([r,[perm3(bb)-1]])
            return np.concatenate([r.real,r.imag])
        n=nF+(9 if freeb else 0)
        z0=rng.normal(size=2*n)*rng.choice([0.3,1.0,2.0])
        if freeb:
            # start b near a structured matrix
            b0=STRUCT[rng.integers(len(STRUCT))].reshape(9)+0.3*(rng.normal(size=9)+1j*rng.normal(size=9))
            z0[nF:nF+9]=b0.real; z0[n+nF:n+nF+9]=b0.imag
        try: sol=least_squares(res,z0,method='lm',max_nfev=400)
        except Exception as e: continue
        r=np.linalg.norm(sol.fun); best=min(best,r)
        if r<1e-9:
            V,bb=unpack(sol.x)
            if np.abs(V).max()<1e4: found+=1; sols.append((V,bb))
    return found,s+1,best,sols
J=np.ones((3,3)); I3=np.eye(3)
STRUCT=[J,I3,np.array([[1,1,0],[1,1,0],[0,0,1.]]),np.array([[1,1,1],[1,1,0],[1,0,0.]]),np.array([[0,1,1],[1,0,1],[1,1,0.]]),
        np.array([[1,1,0],[0,1,1],[1,0,1.]]),np.array([[1,2,3],[1,2,3],[1,2,3.]]),np.array([[1,0,0],[0,1,1],[0,1,-1.]]),
        np.array([[1,1,1],[1,-1,0],[0,0,1.]]),np.array([[2,0,0],[0,0,1],[0,1,0.]]),np.array([[1,1,1],[1,1,1],[0,0,1.]]),
        np.array([[1,0,1],[0,1,0],[1,0,-1.]])]
if __name__=='__main__':
    mode=sys.argv[2] if len(sys.argv)>2 else 'fixed'
    if mode=='fixed':
        for ib,b in enumerate(STRUCT):
            pb=perm3(b.astype(complex).reshape(9))
            f3,n3,b3,_=run(b.astype(complex),3,12,tmax=4)
            f4,n4,b4,_=run(b.astype(complex),4,40,tmax=6)
            print('b#%d perm(b)=%g : dim3 found %d/%d (best res %.1e) ; dim4 found %d/%d (best res %.1e)'%(ib,pb.real,f3,n3,b3,f4,n4,b4),flush=True)
    else:
        f3,n3,b3,_=run(None,3,20,freeb=True,tmax=15)
        print('free b: dim3 found %d/%d (best %.1e)'%(f3,n3,b3),flush=True)
        f4,n4,b4,sols=run(None,4,400,freeb=True,tmax=100)
        print('free b: dim4 found %d/%d (best %.1e)'%(f4,n4,b4),flush=True)
        for V,bb in sols[:3]: print(np.round(bb.reshape(3,3),4)); print(np.round(V,4))
