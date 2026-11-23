import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/chief')
import numpy as np, itertools
from core import nullspace
from testAB_lib import rank, Qf
rng=np.random.default_rng(8)
def rnd(k): return rng.normal(size=k)+1j*rng.normal(size=k)
def report(name,kap,kapp,nu,nup):
    print(name,' <m,J2>: %.1e %.1e'%(abs(kap.sum()-kapp.sum()),abs(nu.sum()+nup.sum())))
    out=[]
    for j,l in itertools.combinations(range(5),2):
        A=np.array([[kap[j],kap[l],-kapp[j],-kapp[l]],[nu[j],nu[l],nup[j],nup[l]]])
        N=nullspace(A); ell=np.array([kap[j],kap[l],0,0])@N
        G=N.T@Qf@N; rk=rank(G,1e-9); B1=abs(ell).max()>1e-9
        ok = (N.shape[1]==2) and ((B1 and rk==1 and True) or (not B1))
        # for B1 also check radical = ker ell
        if B1 and rk==1:
            k=nullspace(ell[None,:]); z=N@k[:,0]; ok = ok and np.abs(N.T@Qf@z).max()<1e-8
        out.append(((j,l),N.shape[1],'B1' if B1 else 'nonB1',rk,'OK' if ok else 'FAIL'))
    print('  ',out)
# Type I
kap=rnd(5); kap/=kap.sum(); C2=[3,4]; C1=[0,1,2]
K1=kap[C1].sum(); K2=kap[C2].sum(); c=1/(K1-K2)
om=np.array([c,c,c,-c,-c]); kapp=om*kap
rho=np.array([0,0,0,1,1.]); s0=-K2*(1+c); rhop=s0-rho
report('Type I',kap,kapp,rho*kap,rhop*kapp)
# Type II: cells Q1={0,1,2} corner (x,y), Q2={3} (x,y'), Q3={4} (x',y), x+y'=x'+y, sigma2=i sigma1
# unknown kap (sum 1), c: omega = (-i c) on Q1? derive: omega_Q1 = c*sigma1/sigma2 = c/i = -i c ; omega_Q2=c, omega_Q3=-c
kap=rnd(5); kap/=kap.sum()
K1=kap[:3].sum(); c=1/(-1j*K1+kap[3]-kap[4]); om=np.array([-1j*c]*3+[c,-c]); kapp=om*kap
# rho=(x,x,x,x,x'), rho'=(y,y,y,y',y): normalise x=0: sigma1=y, sigma2=y'=i y, x'=y'-y ; global: sum kap rho + sum kapp rho' = 0 fixes ratio -> solve for y given scale x'... 
# unknowns y (then y'=iy, x'=(i-1)y): equation kap4*x' + y*(kapp0+kapp1+kapp2+kapp4) + y'*kapp3 = 0 is homogeneous in y -> need coefficient zero: impose by adjusting? check coefficient
coef=kap[4]*(1j-1)+(kapp[:3].sum()+kapp[4])+1j*kapp[3]
print('Type II global coefficient (must vanish for existence): %.3f'%abs(coef))
y=1.0; rho=np.array([0,0,0,0,(1j-1)*y]); rhop=np.array([y,y,y,1j*y,y])
report('Type II (ignoring the global relation)',kap,kapp,rho*kap,rhop*kapp)
