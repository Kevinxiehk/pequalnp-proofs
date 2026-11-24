import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/hessmix')
from hk import *
rng=np.random.default_rng(9)
def Phi(x):
    m,a_,b_,g=parts(x); return g-1.5*ab(a_,b_)
def P4u(u):
    R=u.sum(1); C=u.sum(0); r=(u*u).sum(1); c=(u*u).sum(0); p2=(u*u).sum(); uC=u@C; uR=u.T@R
    return (1.5*(u**4).sum()-0.75*((r*r).sum()+(c*c).sum())+p2**2/8+0.25*np.trace((u@u.T)@(u@u.T))
     -7/108*((R**4).sum()+(C**4).sum())+7/216*((R*R).sum()**2+(C*C).sum()**2)+1/36*(R*R).sum()*(C*C).sum()
     -1/12*p2*((R*R).sum()+(C*C).sum())+0.5*((R*R*r).sum()+(C*C*c).sum())-2/3*((R[:,None]*u**3).sum()+(C[None,:]*u**3).sum())
     +2/9*(R[:,None]*u*u*C[None,:]).sum()-1/9*((R*R*uC).sum()+(C*C*uR).sum())-1/6*((uR*uR).sum()+(uC*uC).sum())
     +1/3*((uC*r).sum()+(uR*c).sum()))
err=0
for _ in range(20):
    t=rng.normal(size=(5,5))+1j*rng.normal(size=(5,5)); t-=t.mean()
    err=max(err,abs(Pk(t)[0,4]-P4u(Phi(t)))/abs(Pk(t)[0,4]))
print('P4 u-formula rel err',err)
def H4delta(dl,s,s2):
    u=Phi(s); v=Phi(s2); R=u.sum(1);C=u.sum(0);R2=v.sum(1);C2=v.sum(0)
    rd=(dl*dl).sum(1); cd=(dl*dl).sum(0); d2=dl*dl
    rho=(dl*u).sum(1); rho2=(dl*v).sum(1); ka=(dl*u).sum(0); ka2=(dl*v).sum(0)
    base=(18*(d2*u*v).sum()-6*(rho*rho2).sum()-3*(rd*(u*v).sum(1)).sum()-6*(ka*ka2).sum()-3*(cd*(u*v).sum(0)).sum()
          +(dl*u).sum()*(dl*v).sum()+0.5*(dl*dl).sum()*(u*v).sum()
          +np.trace(dl.T@dl@u.T@v)+np.trace(dl@u.T@dl@v.T)+np.trace(v.T@dl@dl.T@u))
    corr=(-1/6*(dl*dl).sum()*(R@R2+C@C2)+(rd*R*R2).sum()+(cd*C*C2).sum()
          -2*(d2*(R[:,None]*v+R2[:,None]*u+C[None,:]*v+C2[None,:]*u)).sum()
          +2/9*(d2*(R[:,None]*C2[None,:]+R2[:,None]*C[None,:])).sum()
          -1/3*((dl.T@R)@(dl.T@R2)+(dl@C)@(dl@C2))
          +2/3*((dl@C)@rho2+(dl@C2)@rho+(dl.T@R)@ka2+(dl.T@R2)@ka)
          +1/3*((rd*(v@C+u@C2)).sum()+(cd*(v.T@R+u.T@R2)).sum()))
    return base+corr
err=0
for _ in range(5):
    dl=parts(rng.normal(size=(5,5))+1j*rng.normal(size=(5,5)))[3]
    s=rng.normal(size=(5,5))+1j*rng.normal(size=(5,5)); s-=s.mean()
    s2=rng.normal(size=(5,5))+1j*rng.normal(size=(5,5)); s2-=s2.mean()
    H=hess_full(dl,4); ref=s.ravel()@H@s2.ravel()
    err=max(err,abs(ref-H4delta(dl,s,s2))/abs(ref))
print('H4 at arbitrary DC delta: rel err',err)
