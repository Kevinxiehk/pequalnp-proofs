# verify2: independent test of verifyfl's THEOREM SPLIT on fresh data.
# Build 2- and 3-dim spaces L' = span(e_i m^T, Y_1[, Y_2]) of 4x5 matrices with defect line C m (C(Y) - 24*1 in C m for all Y in L') by LM,
# then test the conclusion: thetahat = 0 on ker kappa, i.e. ker kappa is strongly level.  Expect: always for <m,m> != 0; failures for isotropic m.
import numpy as np, itertools, sys, time
from scipy.optimize import least_squares
rng=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0)
P4=list(itertools.permutations(range(4)))
def perm4(A): return sum(A[0,p[0]]*A[1,p[1]]*A[2,p[2]]*A[3,p[3]] for p in P4)
def Cvec(Y):
    M=1+Y; return np.array([perm4(np.delete(M,j,axis=1)) for j in range(5)])
def search(m,k,i=3,nstart=12,tmax=25):
    """k extra basis vectors; returns list of bases (k+1) x 4 x 5"""
    mb=m.conj()/np.vdot(m,m); t0=time.time(); out=[]
    B0=np.zeros((4,5),complex); B0[i]=m
    S=rng.normal(size=(14,k+1))+1j*rng.normal(size=(14,k+1))
    def res(z):
        Ys=(z[:20*k]+1j*z[20*k:]).reshape(k,4,5); r=[]
        for s in S:
            Y=s[0]*B0+np.tensordot(s[1:],Ys,1); c=Cvec(Y)-24; c=c-(mb@c)*m; r+=[c.real,c.imag]
        # keep the new vectors away from e_i m^T and normalised
        G=np.array([np.vdot(Ys[a],Ys[b]) for a in range(k) for b in range(k)]).reshape(k,k)-np.eye(k)
        return np.concatenate(r+[G.real.ravel(),G.imag.ravel(),[np.vdot(B0,Ys[a]).real for a in range(k)],[np.vdot(B0,Ys[a]).imag for a in range(k)]])
    for st in range(nstart):
        if time.time()-t0>tmax: break
        sol=least_squares(res,rng.normal(size=40*k)*0.4,method='lm',max_nfev=1500)
        if np.linalg.norm(sol.fun)<1e-10: out.append(np.concatenate([B0[None],(sol.x[:20*k]+1j*sol.x[20*k:]).reshape(k,4,5)]))
    return out
def kappa(Y,m): 
    g=Y.sum(axis=0); return np.vdot(m,g)/np.vdot(m,m), np.linalg.norm(g-(np.vdot(m,g)/np.vdot(m,m))*m)
w=np.exp(2j*np.pi/3)
tests=[('(1,2,-3,0,0)',np.array([1,2,-3,0,0],complex)),('(1,1,-2,0,0)',np.array([1,1,-2,0,0],complex)),('(1,2,3,-1,-5)',np.array([1,2,3,-1,-5],complex)),
       ('(1,-1,0,0,0)',np.array([1,-1,0,0,0],complex)),('(1,i,2,-3-i,0)',np.array([1,1j,2,-3-1j,0],complex)),
       ('ISOTROPIC (1,w,w^2,0,0)',np.array([1,w,w*w,0,0],complex)),('ISOTROPIC (1,i,-1,-i,0)',np.array([1,1j,-1,-1j,0],complex))]
sel=[int(x) for x in sys.argv[2].split(",")] if len(sys.argv)>2 else range(len(tests))
for name,m in [tests[q] for q in sel]:
    for k in ((1,) if len(sys.argv)>3 else (1,2)):
        sp=search(m,k,nstart=14 if k==1 else 8,tmax=30 if len(sys.argv)>3 else (9 if k==1 else 12)); worst=0; nbad=0; gam=0
        for Bs in sp:
            # ker kappa: combinations with zero column sums
            ks=[kappa(Y,m) for Y in Bs]; gam=max(gam,max(x[1] for x in ks))
            K=[Bs[a]-ks[a][0]*Bs[0] for a in range(1,k+1)]       # kappa(B0) = 1
            err=0
            for _ in range(4):
                c=rng.normal(size=k)+1j*rng.normal(size=k); Y=np.tensordot(c,np.array(K),1); err=max(err,np.abs(Cvec(Y)-24).max())
            worst=max(worst,err); nbad+=err>1e-6
        print('m = %-26s <m,m> = %-12s dim %d: spaces found %2d, column sums off C m: %.0e, ker kappa NOT strongly level in %d (max |C - 24| on ker kappa: %.1e)'
              %(name,np.round(m@m,3),k+1,len(sp),gam,nbad,worst),flush=True)
