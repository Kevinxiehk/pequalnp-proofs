# The cyclic Type II triple: are the J-relations (J_3 in I_3, i.e. the three pair relations evaluated at tau_i = kappa^i,
# plus sum kappa^i = 1) solvable?  Only block sums of kappa^1 enter.
import sys, itertools, numpy as np; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
from t6_typeII_full import typeII
rng=np.random.default_rng(0)
surv=[(((0,1,2,2,2),1),((2,1,0,0,0),1),((2,0,1,1,1),1)),(((0,1,1,1,2),1),((2,1,1,1,0),1),((2,0,0,0,1),1)),
      (((0,0,0,1,2),1),((2,2,2,1,0),1),((2,2,2,0,1),1)),(((0,1,1,2,2),1),((2,1,1,0,0),1),((2,0,0,1,1),1)),
      (((0,0,1,2,2),1),((2,2,1,0,0),1),((2,2,0,1,1),1)),(((0,0,1,1,2),1),((2,2,1,1,0),1),((2,2,0,0,1),1))]
def resid(x,s12,s13,s23):
    k1=x[:5]; c2,c3=x[5],x[6]
    w2,A1,A2,y12=typeII(*s12); w3,B1,B3,y13=typeII(*s13); w23,C2,C3,y23=typeII(*s23)
    k2=c2*w2*k1; k3=c3*w3*k1
    return np.array([k1.sum()-1,k2.sum()-1,k3.sum()-1, A1@k1+A2@k2+y12, B1@k1+B3@k3+y13, C2@k2+C3@k3+y23])
def solve(s):
    best=1e9
    for trial in range(60):
        x=rng.normal(size=7)+1j*rng.normal(size=7)
        for it in range(60):
            r=resid(x,*s); 
            Jm=np.zeros((6,7),complex); h=1e-7
            for k in range(7):
                e=np.zeros(7,complex); e[k]=h; Jm[:,k]=(resid(x+e,*s)-r)/h
            dx=np.linalg.lstsq(Jm,-r,rcond=None)[0]; x=x+dx
            if np.linalg.norm(dx)<1e-13: break
        best=min(best,np.linalg.norm(resid(x,*s)))
    return best
for s in surv:
    # consistency of the (2,3) ratio with the listed structure
    w2=typeII(*s[0])[0]; w3=typeII(*s[1])[0]; w23=typeII(*s[2])[0]; r=(w3/w2)/w23
    print(s,' ratio check (const):',np.allclose(r,r[0]),' min residual of J-relations over 60 Newton runs: %.3e'%solve(s))
# hand elimination: c2=c3=c must satisfy both  c^2 + i c - (1+i)/4 = 0  and  c^2 + 2 i c - (1+i)/2 = 0
c=(1-1j)/4; print('common root candidate c=(1-i)/4: values',c*c+1j*c-(1+1j)/4, c*c+2j*c-(1+1j)/2)
