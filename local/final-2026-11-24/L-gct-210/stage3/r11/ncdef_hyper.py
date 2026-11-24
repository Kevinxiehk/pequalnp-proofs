# members with w2 o w3 = la w2 + mu w3 (points (w2_j, w3_j), j = 1..4, on the hyperbola (x - mu)(y - la) = la mu): is dim T_1 = 13 there?
import sys, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r11'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/verify2'); import fo2lib as F
exec(open('/home/kevxhk/work/L-gct-210/stage3/r11/ncdef_locus.py').read().split('cases={}')[0])
def hyper_member():
    la,mu=rg.normal(size=2)+1j*rg.normal(size=2); y1,y2=rg.normal(size=2)+1j*rg.normal(size=2)
    S=-(y1+y2); R=-(y1/(y1-la)+y2/(y2-la))
    # y3 (S - y3 - la) + (S - y3)(y3 - la) = R (y3 - la)(S - y3 - la)   -> quadratic in y3
    P=np.polynomial.polynomial
    lhs=P.polyadd(P.polymul([0,1],[S-la,-1]),P.polymul([S,-1],[-la,1]))
    rhs=R*P.polymul([-la,1],[S-la,-1]); y3=P.polyroots(P.polysub(lhs,rhs))[0]; y4=S-y3
    y=np.array([y1,y2,y3,y4]); x=mu*y/(y-la)
    w2=np.r_[0,x]; w3=np.r_[0,y]; return w2,w3
for _ in range(4):
    w2,w3=hyper_member(); B=member(w2,w3)
    lev=max(abs(F.perm_small(J+np.tensordot(rg.normal(size=5)+1j*rg.normal(size=5),B,axes=1))-120) for _ in range(5))
    t=T1dim(B); print('hyperbola member: sum w2 %.0e sum w3 %.0e <w2,w3> %.0e  level %.0e  dim T_1 = %d (gap %.0e)'%(abs(w2.sum()),abs(w3.sum()),abs(w2@w3),lev,t[0],t[1]))
