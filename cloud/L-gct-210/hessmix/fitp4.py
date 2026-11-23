import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/hessmix')
from hk import *
from fractions import Fraction
rng=np.random.default_rng(4)
def Phi(x):
    m,a_,b_,g=parts(x); return g-1.5*ab(a_,b_)
def feats(u):
    R=u.sum(1); C=u.sum(0); r=(u*u).sum(1); c=(u*u).sum(0); p2=(u*u).sum()
    uC=u@C; uR=u.T@R
    base=1.5*(u**4).sum()-0.75*((r*r).sum()+(c*c).sum())+p2**2/8+0.25*np.trace((u@u.T)@(u@u.T))
    F=[ (R**4).sum()+(C**4).sum(), (R*R).sum()**2+(C*C).sum()**2, (R*R).sum()*(C*C).sum(), p2*((R*R).sum()+(C*C).sum()),
        (R*R*r).sum()+(C*C*c).sum(), (R[:,None]*u**3).sum()+(C[None,:]*u**3).sum(), (R[:,None]*u*u*C[None,:]).sum(),
        (R[:,None]**2*u*C[None,:]).sum()+(R[:,None]*u*C[None,:]**2).sum(), (uR*uR).sum()+(uC*uC).sum(),
        (R*R*uC).sum()+(C*C*uR).sum(), (uC*r).sum()+(uR*c).sum()]
    return base,np.array(F)
names=['R4','(R2)^2','R2C2','p2R2','R2r','Ru3','RuuC','R2uC','|u^T R|^2','R^2(uC)','(uC)r']
rows=[];rhs=[]
for _ in range(60):
    t=rng.normal(size=(5,5))+1j*rng.normal(size=(5,5)); t-=t.mean()
    u=Phi(t); b,F=feats(u); rows.append(F); rhs.append(Pk(t)[0,4]-b)
A=np.array(rows); y=np.array(rhs)
x,res,rk,s=np.linalg.lstsq(A,y,rcond=None)
print('rank',rk,'resid',np.abs(A@x-y).max())
for n_,v in zip(names,x): print(n_, v.real, Fraction(v.real).limit_denominator(5000))
