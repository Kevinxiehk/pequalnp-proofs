# calibration of the (alpha1) supp-3 systems: the degree-<=2 truncation is equivalent to A_4^*A_4 = 5 - 4 rho^2 f (x) f with
# A_4 = -3 - sum_{j<=3} A_j in the normal form; find a numerical solution (=> truncation non-unit), then check the full degree-3/4 conditions FAIL.
import numpy as np, itertools
rg=np.random.default_rng(3); I=1j
chi=[np.array([I**(k*r) for r in range(4)]) for k in range(4)]
def vec(a,b,c): return a*chi[1]+b*chi[2]+c*chi[3]
G=lambda x,y: x@y                                    # bilinear form on V (inside C^4)
B=np.array([chi[1],chi[2],chi[3]]).T                 # 4x3 basis of V
v=chi[1]; e=chi[2]/2; eps=[1,1,1,1]
def ops(x):
    p1,p2,ph,fc=x[0:3],x[3:6],x[6:9],x[9:12]; rho,tau=x[12],x[13]
    psi=[np.zeros(4,complex),vec(*p1),vec(*p2)]; phi=vec(*ph); f=vec(*fc)
    n=vec(1,2*tau,-2*tau**2); e3=vec(0,0.5,-tau)
    A=[np.outer(v,psi[j])+eps[j]*rho*np.outer(e,f) for j in range(3)]+[np.outer(n,phi)+eps[3]*rho*np.outer(e3,f)]
    return A,f,rho
def F(x):
    A,f,rho=ops(x); A4=-3*np.eye(4)-sum(A)
    # bilinear identity on V: <A4 y, A4 y'> = 5 <y,y'> - 4 rho^2 <f,y><f,y'>  for y, y' in V (basis B)
    lhs=(A4@B).T@(A4@B); rhs=5*B.T@B-4*rho**2*np.outer(B.T@f,B.T@f)
    d=lhs-rhs; return np.array([d[i,j] for i in range(3) for j in range(i,3)]+[x[9]-1.0])    # f chart
def J(x,h=1e-7):
    f0=F(x); Jm=np.empty((len(f0),len(x)),complex)
    for i in range(len(x)):
        dd=np.zeros(len(x),complex); dd[i]=h; Jm[:,i]=(F(x+dd)-f0)/h
    return f0,Jm
for st in range(10):
    x=rg.normal(size=14)+1j*rg.normal(size=14); lam=1e-3
    f0,Jm=J(x); nf=np.linalg.norm(f0)
    for it in range(200):
        A_=Jm.conj().T@Jm; g=Jm.conj().T@f0; d=np.linalg.solve(A_+lam*np.eye(14),g); f2=F(x-d)
        if np.linalg.norm(f2)<nf: x=x-d; f0,Jm=J(x); nf=np.linalg.norm(f0); lam=max(lam/4,1e-15)
        else: lam*=4
        if nf<1e-13: break
    if nf<1e-11:
        print('quadratic-level solution found (start %d): residual %.1e, rho = %s'%(st,nf,np.round(x[12],4))); break
else: print('no quadratic-level solution found')
