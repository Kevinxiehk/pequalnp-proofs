# numerical search, support-4 (2,1) kernels in the Cramer-reduced normal form (5 complex unknowns s0..s4 per sign pattern ep1..ep4)
import numpy as np, itertools, sys
from scipy.optimize import least_squares
H=np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],float); I=1j
rng=np.random.default_rng(int(sys.argv[1])); NST=int(sys.argv[2])
P4=np.array(list(itertools.permutations(range(4))))
YY=rng.normal(size=(14,3))+1j*rng.normal(size=(14,3))
cc=lambda s: np.array([s*s-1,I*(s*s+1),2*s]); cd=lambda s: np.array([s,I*s,1])
def parts(Y):
    G=Y.T@Y; Sall=(G.sum()-np.trace(G))/2; out=[]
    for k in range(5):
        idx=[j for j in range(5) if j!=k]; Yk=Y[:,idx]
        e1=Yk.sum(1); p2r=(Yk**2).sum(1); p3r=(Yk**3).sum(1)
        out+=[2*((e1**3-3*e1*p2r+2*p3r)/6).sum(), np.prod(Yk[np.arange(4)[None,:],P4],axis=1).sum(), -2*(Sall-(G[k].sum()-G[k,k]))]
    return np.array(out)
def build(s,ep):
    u=cc(s[0]); w=cd(s[0]); f=[cc(s[k]) for k in range(1,5)]; F=np.array(f[1:]).T
    al=np.r_[0,np.linalg.solve(F,2*u)]; be=np.r_[1,np.linalg.solve(F,-f[0])]
    mu=np.r_[0,np.linalg.solve(F,2*w-sum(ep[k]*cd(s[k+1]) for k in range(4)))]
    m=[ep[k]*cd(s[k+1])+mu[k]*f[k] for k in range(4)]
    A1=[(u-al[k]*f[k])/2 for k in range(4)]+[np.zeros(3)]; A2=[(w-m[k])/2 for k in range(4)]+[np.zeros(3)]; A3=[-be[k]*f[k]/2 for k in range(4)]+[np.zeros(3)]
    return A1,A2,A3
def res(x,ep):
    s=x[:5]+1j*x[5:]
    try: A1,A2,A3=build(s,ep)
    except np.linalg.LinAlgError: return np.ones(14*15*2)*1e3
    r=[]
    for y in YY:
        Y=H@np.array([y[0]*A1[k]+y[1]*A2[k]+y[2]*A3[k] for k in range(5)]).T
        p=parts(Y); r+=list(p[0::3])+list(p[1::3])+list(p[2::3]*0)
    r=np.array(r); return np.r_[r.real,r.imag]
best=[]
for ep in itertools.product((1,-1),repeat=4):
    if ep[0]==-1 and False: pass
    for st in range(NST):
        sol=least_squares(res,rng.normal(size=10),args=(ep,),xtol=1e-14,ftol=1e-14,gtol=1e-14,max_nfev=3000)
        nr=np.linalg.norm(res(sol.x,ep)); best.append(nr)
        if nr<1e-7:
            s=sol.x[:5]+1j*sol.x[5:]; A1,A2,A3=build(s,ep)
            ranks=[int(np.linalg.matrix_rank(np.array([A1[k],A2[k],A3[k]]),1e-6)) for k in range(5)]
            print('ep',ep,'start',st,'SOLUTION res %.1e column ranks %s s=%s'%(nr,ranks,np.round(s,4)),flush=True)
print('min residual over all starts: %.2e; median %.2e; n=%d'%(min(best),np.median(best),len(best)))
