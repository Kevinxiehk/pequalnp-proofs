import sys; sys.path.insert(0,'.')
from bank import *
def info(L,tol=1e-7):
    L=np.asarray(L); Lf=L.reshape(len(L),-1); Q,_=np.linalg.qr(Lf.T); B=Q.T.reshape(len(L),5,5)  # orthonormal basis
    c,al,be,g=decomp(B)
    def rk(M):
        s=np.linalg.svd(M,compute_uv=False); return int((s>tol).sum())
    r=rk(np.concatenate([al,be],1)); rA=rk(al); rB=rk(be); d=len(L)-r
    return dict(dim=len(L),r=r,rA=rA,rB=rB,d=d,minpd=min(rA,rB)+d,RcapA=r-rB,RcapB=r-rA)
if __name__=='__main__':
    for k,B in bank.items(): print(k,info(B))
    for f in ['split/rc45p1.npy','split/d1_ext1.npy','numerics/W5ext_dc0_e1.npy','numerics/S5_w5ext_s2_0.npy','numerics/S4_w5ext_s2_0.npy']:
        print(f,info(np.load('/home/claude/work/L-gct-210/'+f)))
