import numpy as np, itertools, math
SUB=np.array([[ (m>>j)&1 for j in range(5)] for m in range(32)],float)   # 32 x 5
SG=np.array([(-1)**(5-int(r.sum())) for r in SUB])
def permb(M):  # batch (...,5,5)
    rs=M@SUB.T            # (...,5,32)
    return (np.prod(rs,axis=-2)*SG).sum(-1)
OM=np.exp(2j*np.pi*np.arange(6)/6)
FACT=np.array([math.factorial(5-k) for k in range(6)])
def Pall(T):  # T (...,5,5) -> (...,6) P_0..P_5
    vals=np.stack([permb(1+s*T) for s in OM],-1)   # (...,6) = sum_k (5-k)! P_k s^k
    coef=np.fft.fft(vals,axis=-1)/6   # fft: sum_m vals_m e^{-2pi i mk/6} -> coefficient k
    return coef/FACT
if __name__=='__main__':
    import sys; sys.path.insert(0,'.'); from core import Pk
    T=np.random.randn(5,5)+1j*np.random.randn(5,5)
    print([abs(Pall(T)[k]-Pk(T,k)) for k in range(6)])
