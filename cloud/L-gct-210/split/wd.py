import sys; sys.path.insert(0,'.'); sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases')
from core import *
from tangent import weight_space
def rank(M,tol=1e-8):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol*s[0]).sum()) if s.size and s[0]>0 else 0
def nullsp(M,tol=1e-8):
    u,s,vh=np.linalg.svd(M); r=int((s>tol*s[0]).sum()); return vh[r:].conj()  # rows span {x: M x=0}
def analyze(D,nsamp=60,seed=0,ks=(1,2,3,4,5),verbose=True):
    rng=np.random.default_rng(seed); d=len(D)
    c=rnd((nsamp,d),rng); T=np.einsum('rk,kij->rij',c,D)
    P,G=level.Pk_grad(T)
    res=np.abs(P[:,1:]).max()
    W=np.concatenate([G[:,k].reshape(nsamp,25) for k in ks])
    w=rank(W)
    Y=nullsp(W)   # basis rows y with W y = 0 (bilinear, no conj): careful
    # we need y with sum_ab W_ab y_ab = 0 (bilinear). nullsp gives vh rows conj -> M @ x =0 with x = vh.conj() row
    # Q on Y: 2P2(t)=<t,Phi5 t>, Phi5 t = t-5a
    def Phi(t,cf):
        cc,al,be,g=decomp(t.reshape(-1,5,5)); return (g+(1-cf)*ab(al,be)+cc[:,None,None]).reshape(len(t),-1)
    Yb=Y
    Qm=Yb@Phi(Yb,5).T
    rho=Yb.shape[0]-rank(Qm)
    dimY=Yb.shape[0]
    # r part of Y : projection of Y to AB
    cc,al,be,g=decomp(Yb.reshape(-1,5,5)); rY=rank(np.concatenate([al,be],1))
    if verbose: print(f'd={d} res={res:.1e} rank W_D={w} dimY={dimY} rad(Q|Y)={rho} bound (dimY+rho)//2={(dimY+rho)//2}  AB-rank of Y={rY}')
    return w,dimY,rho
if __name__=='__main__':
    W3=weight_space(5,[1,2,3,4,0],[1,2,0,4,3],30,[2,3,4])
    print('weight space dims',len(W3))
    analyze(W3)
    for E in ([2],[3],[4],[2,3],[2,4],[3,4]):
        Wd=weight_space(5,[1,2,3,4,0],[1,2,0,4,3],30,E); print('E',E,end=' '); analyze(Wd)
    rng=np.random.default_rng(5)
    for dd in (1,2):
        c=rnd((dd,3),rng); print('random sub dim',dd,end=' '); analyze(np.einsum('qk,kij->qij',c,W3))
    S2=np.load('/home/claude/work/L-gct-086/smallcases/sol_n5_d2_dc_s5.npy'); print('LM d2',end=' '); analyze(S2)
    for q in range(2):
        print('LM d2 line',end=' '); analyze(S2[q:q+1])
