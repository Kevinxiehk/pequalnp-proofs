import sys, math, itertools
sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases')
import numpy as np, level
n=5
def decomp(T):
    T=np.asarray(T); c=T.mean(axis=(-1,-2),keepdims=True)
    al=T.mean(axis=-1)-c[...,0]; be=T.mean(axis=-2)-c[...,0]
    g=T-c-al[...,:,None]-be[...,None,:]
    return c[...,0,0],al,be,g
def ab(al,be): return al[...,:,None]+be[...,None,:]
def Pk(T): return level.Pk(np.asarray(T))
def rnd(shape,rng): return rng.normal(size=shape)+1j*rng.normal(size=shape)
def dcrand(rng,m=None):
    X=rnd((n,n) if m is None else (m,n,n),rng)
    _,a,b,g=decomp(X); return g
def sz(rng,m=None):
    x=rnd((n,) if m is None else (m,n),rng); return x-x.mean(-1,keepdims=True)
def bideg(k,A,G,da,dg):
    # component of P_k(A+G) of degree da in A, dg in G (da+dg=k); via interpolation in s
    ss=np.exp(2j*np.pi*np.arange(k+1)/(k+1))
    vals=np.array([Pk(s*A+G)[0,k] for s in ss])
    # P_k(sA+G)=sum_m s^m c_m
    coef=np.fft.fft(vals)/(k+1)  # c_m = (1/(k+1)) sum vals * s^{-m}
    # fft computes sum vals*exp(-2pi i m j/(k+1)) = sum vals*s^{-m}
    return coef[da]
def span_info(B,tol=1e-6):
    B=np.asarray(B).reshape(len(B),-1)
    s=np.linalg.svd(B,compute_uv=False); return int((s>tol*s[0]).sum()),s
def rde(B,tol=1e-7):
    """B: (m,5,5) basis of L (entry-sum zero). returns r,d,e and bases"""
    B=np.asarray(B); m=len(B)
    c,al,be,g=decomp(B)
    AB=np.concatenate([al,be],axis=1)  # m x 10
    u,s,vh=np.linalg.svd(AB); r=int((s>tol*max(1,s[0])).sum())
    # kernel of AB-projection within L: coefficients
    N=vh.conj().T  # not used
    U,S,Vh=np.linalg.svd(AB.T)  # AB.T (10 x m); null space of AB.T as map coeff->AB
    rk=int((S>tol*max(1,S[0])).sum())
    ker=Vh[rk:].conj()  # rows: coefficient vectors c with sum c_k AB_k=0
    D=np.einsum('qk,kij->qij',ker,B)
    Gf=g.reshape(m,-1)
    U2,S2,Vh2=np.linalg.svd(Gf.T); rk2=int((S2>tol*max(1,S2[0])).sum())
    kerg=Vh2[rk2:].conj(); E=np.einsum('qk,kij->qij',kerg,B)
    return dict(r=r,d=m-r,e=m-rk2,D=D,E=E,sAB=s,sG=S2)
