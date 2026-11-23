import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/chief')
from core import *
from testAB_lib import hat, rank
pairs=list(itertools.combinations(range(5),2)); trip=list(itertools.combinations(range(5),3))
def p2(a): return a[0,0]*a[1,1]+a[0,1]*a[1,0]
def p3(a): return (a[0,0]*(a[1,1]*a[2,2]+a[1,2]*a[2,1])+a[0,1]*(a[1,0]*a[2,2]+a[1,2]*a[2,0])+a[0,2]*(a[1,0]*a[2,1]+a[1,1]*a[2,0]))
def rhos(Bh,rng,npts2=90,npts3=330):
    m=len(Bh)
    def pts(k): 
        c=rng.normal(size=(k,m))+1j*rng.normal(size=(k,m)); return np.tensordot(c,Bh,1)
    U=pts(npts2); A2=np.array([[p2(u[np.ix_(S,T)]) for S in pairs for T in pairs] for u in U])
    U=pts(npts3); A3=np.array([[p3(u[np.ix_(S,T)]) for S in trip for T in trip] for u in U])
    return rank(A2,1e-9),rank(A3,1e-9)
if __name__=='__main__':
    rng=np.random.default_rng(3)
    from math import comb
    for name,f in list(SP.items())+[('L9(not level)',L9)]:
        B=f(); Bh=hat(B); m=len(Bh)
        r2,r3=rhos(Bh,rng)
        print('%-14s dim L^=%d  S2=%d S3=%d  rho2=%d rho3=%d  rho2+rho3=%d  K2=%d'%(name,m,comb(m+1,2),comb(m+2,3),r2,r3,r2+r3,comb(m+1,2)-r2))
    # random sum-zero spaces + J
    for l in (7,8,9):
        B=rng.normal(size=(l,5,5))+1j*rng.normal(size=(l,5,5)); B=B-B.mean(axis=(1,2),keepdims=True)
        Bh=hat(B); m=len(Bh); r2,r3=rhos(Bh,rng)
        print('random l=%d  S2=%d S3=%d rho2=%d rho3=%d'%(l,comb(m+1,2),comb(m+2,3),r2,r3))
