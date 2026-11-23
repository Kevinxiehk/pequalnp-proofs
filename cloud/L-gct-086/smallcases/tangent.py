import sys; sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases')
from level import *
def ext_space_dim(Tb, n, nsamp=None, seed=0):
    """dim of {t : D P_k(l)[t]=0 for all l in L, k=1..n}  (contains every level L' >= L)."""
    rng=np.random.default_rng(seed); d=len(Tb)
    nsamp = nsamp or 400
    xs=rng.normal(size=(nsamp,d))+1j*rng.normal(size=(nsamp,d))
    T=np.einsum('ri,iab->rab',xs,Tb)
    P,G=Pk_grad(T)
    rows=G[:,1:].reshape(-1,n*n)
    nr=np.linalg.norm(rows,axis=1); rows=rows[nr>1e-9*nr.max()]
    rows=rows/np.linalg.norm(rows,axis=1,keepdims=True)
    s=np.linalg.svd(rows,compute_uv=False)
    return n*n-np.sum(s>1e-8*s[0]), s
def weight_space(n, sigma, tau, N, E):
    z=np.exp(2j*np.pi/N); out=[]
    # orbits of (i,j) under g=(sigma,tau)
    seen=set()
    for i in range(n):
        for j in range(n):
            if (i,j) in seen: continue
            orb=[(i,j)]; a,b=i,j
            while True:
                a,b=sigma[a],tau[b]
                if (a,b)==(i,j): break
                orb.append((a,b))
            seen.update(orb); l=len(orb)
            for e in E:
                if (e*l)%N==0:
                    T=np.zeros((n,n),complex)
                    for s,(a,b) in enumerate(orb): T[a,b]=z**(e*s)
                    out.append(T)
    return np.array(out)
if __name__=='__main__':
    for n in range(3,7):
        B=np.array(construction_2n3(n),dtype=complex)
        dT,s=ext_space_dim(B,n)
        print('2n-3 construction n=%d dim %d, first-order extension space dim %d'%(n,len(B),dT))
