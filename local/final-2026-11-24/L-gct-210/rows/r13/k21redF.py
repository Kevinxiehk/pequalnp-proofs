# (2,1) strongly level kernels in the REDUCED form of Lemma R13.6: rho(K) = u^perp (u isotropic), basis e1, e2, n of K with rho e1 = u,
# rho e2 = w (w.w = 1, w.u = 0), rho n = 0;  M_k := rho - 2 A_k satisfies M_k^T M_k = rho^T rho, hence
# M_k e1 = al_k f_k, M_k e2 = m_k, M_k n = be_k f_k  (f_k isotropic, m_k unit, m_k.f_k = 0),  sum_k M_k = 3 rho.
# Degree 2 is automatic; we solve the degree-3 and degree-4 conditions numerically and record supports.  (Walsh coordinates.)
import numpy as np, itertools, sys
from scipy.optimize import least_squares
H=np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],float)
rng=np.random.default_rng(int(sys.argv[1])); NST=int(sys.argv[2]); SUP=int(sys.argv[3]) if len(sys.argv)>3 else 5
P4=np.array(list(itertools.permutations(range(4))))
YY=rng.normal(size=(16,3))+1j*rng.normal(size=(16,3))
NV=3+3+15+15+5+5
def unpack(z):
    u=z[0:3]; w=z[3:6]; f=z[6:21].reshape(5,3); m=z[21:36].reshape(5,3); al=z[36:41]; be=z[41:46]; return u,w,f,m,al,be
def cols(z):
    u,w,f,m,al,be=unpack(z)
    A1=[(u-al[k]*f[k])/2 for k in range(5)]; A2=[(w-m[k])/2 for k in range(5)]; A3=[-be[k]*f[k]/2 for k in range(5)]
    return A1,A2,A3
def parts(Y):
    G=Y.T@Y; Sall=(G.sum()-np.trace(G))/2; out=[]
    for k in range(5):
        idx=[j for j in range(5) if j!=k]; Yk=Y[:,idx]
        p2=-2*(Sall-(G[k].sum()-G[k,k])); e1=Yk.sum(1); p2r=(Yk**2).sum(1); p3r=(Yk**3).sum(1)
        p3=2*((e1**3-3*e1*p2r+2*p3r)/6).sum(); p4=np.prod(Yk[np.arange(4)[None,:],P4],axis=1).sum()
        out+=[p2,p3,p4]
    return np.array(out)
rr=rng.normal(size=(8,3))+1j*rng.normal(size=(8,3)); cz=rng.normal(size=(5,9))+1j*rng.normal(size=(5,9))
def res(x):
    z=x[:NV]+1j*x[NV:]; u,w,f,m,al,be=unpack(z); r=[]
    r+=[u@u,u@w,w@w-1]; r+=[f[k]@f[k] for k in range(5)]+[m[k]@f[k] for k in range(5)]+[m[k]@m[k]-1 for k in range(5)]
    r+=list(sum(al[k]*f[k] for k in range(5))-3*u)+list(sum(m)-3*w)+list(sum(be[k]*f[k] for k in range(5)))
    r+=[be[0]-1, al[0], rr[0]@u-1]+[rr[1+k]@f[k]-1 for k in range(4)]+[rr[6]@m[0]]+([rr[5]@f[4]-1] if SUP==5 else [])
    NZ=5 if SUP==5 else 4
    if SUP==4: r+=list(al[4]*f[4]-u)+list(m[4]-w)+[be[4]]      # column 5 zero
    for k in range(NZ):   # force column k nonzero: a random functional of (al f - u, m - w, be f) equals 1
        r+=[cz[k,0:3]@(al[k]*f[k]-u)+cz[k,3:6]@(m[k]-w)+cz[k,6:9]@(be[k]*f[k])-1]
    A1,A2,A3=cols(z)
    for y in YY:
        Y=H@np.array([y[0]*A1[k]+y[1]*A2[k]+y[2]*A3[k] for k in range(5)]).T
        r+=list(parts(Y))
    r=np.array(r); return np.r_[r.real,r.imag]
from collections import Counter
C=Counter()
for st in range(NST):
    sol=least_squares(res,rng.normal(size=2*NV),xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=4000)
    nr=np.linalg.norm(res(sol.x))
    if nr>1e-8: C['nonconv']+=1; print('start %d nonconv %.1e'%(st,nr),flush=True); continue
    z=sol.x[:NV]+1j*sol.x[NV:]; A1,A2,A3=cols(z)
    ranks=[int(np.linalg.matrix_rank(np.array([A1[k],A2[k],A3[k]]),1e-6)) for k in range(5)]
    C[tuple(sorted(ranks,reverse=True))]+=1
    print('start %d: column ranks %s support %d'%(st,ranks,sum(x>0 for x in ranks)),flush=True)
    np.save('k21red_%s_%d_%d.npy'%(sys.argv[1],SUP,st),z)
print(C)
