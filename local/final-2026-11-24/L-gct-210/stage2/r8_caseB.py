# Case B of the (2,4) family, sub-case (B1) (a, b independent on X): explicit parametrisation and Omega.
#   X = C xi_d (+) X_0,  xi_d = (e_1 - e_2) e_0^T,  X_0 <-> Y_0 = maximal isotropic subspace of (p',q') in C^4 x C^4 for p'^T K q', K = J - I,
#   Y_0 = {(p',q') : p' in A', K q' = W-part + A'^perp},  p_0 = -a-(1+mu) b, q_0 = (mu-1) a - b, s = (1-mu) a + (1+mu) b, s_1 = s_2 = s/2.
# Compare dim Omega from the general T_1 tool (r7_FOrow) with the reduced criterion
#   Omega = C e_0 (+) {(0,v): s*gamma_v in D_0}.
import sys, itertools, numpy as np
P4=np.array(list(itertools.permutations(range(4))))
def perm4(A): return A[...,np.arange(4)[None,:],P4].prod(axis=-1).sum(axis=-1)
COLS=[[c for c in range(5) if c!=j] for j in range(5)]
def G(Y): return np.stack([perm4(Y[...,:,cols]) for cols in COLS],axis=-1)
def cof55(M):
    out=[]
    for i in range(5):
        for j in range(5):
            A=np.delete(np.delete(M,i,axis=0),j,axis=1); out.append(A[np.arange(4)[None,:],P4].prod(axis=1).sum())
    return out
rgT=np.random.default_rng(1)
def T1(X):
    Mb=X.reshape(len(X),25); rows=[cof55(np.ones((5,5))+((rgT.normal(size=len(X))+1j*rgT.normal(size=len(X)))@Mb).reshape(5,5)) for _ in range(70)]
    u,s,vh=np.linalg.svd(np.array(rows)); r=int((s>1e-8*s[0]).sum()); return vh[r:].conj()
def rk(M):
    s=np.linalg.svd(M,compute_uv=False); return int((s>1e-7).sum())
def report(name,B):
    X=np.zeros((len(B),5,5),complex); X[:,1:,:]=B; T=T1(X); Tm=T.reshape(len(T),5,5); pr=rk(Tm[:,0,:])
    print('%-24s dim T_1 = %2d, dim Omega (row-r projection) = %d'%(name,len(T),pr),flush=True)
K=np.ones((4,4))-np.eye(4); Ki=np.ones((4,4))/3-np.eye(4)
def buildY0(Ap,W):
    """Ap: k x 4 basis of A'; W: k x k skew. returns list of (p',q') spanning Y_0 (4 vectors)."""
    k=len(Ap); out=[]
    # dual vectors w_i with <w_i, alpha_j> = W_ij
    G=Ap@Ap.T; D=np.linalg.solve(G,Ap)           # rows: dual basis within A' (bilinear)
    for i in range(k):
        wi=W[i]@D; out.append((Ap[i],Ki@wi))
    u,s,vh=np.linalg.svd(Ap); perp=vh[k:]        # A'^perp w.r.t. bilinear pairing: null space of Ap (complex: use Ap, not conj)
    # bilinear orthogonal complement: solve Ap n = 0
    ns=np.linalg.svd(Ap)[2][k:].conj()
    for n in ns: out.append((np.zeros(4,complex),Ki@n))
    return out
def buildX(mu,Y0):
    B=[]
    M=np.zeros((4,5),complex); M[0,0]=1; M[1,0]=-1; B.append(M)
    for (p,q) in Y0:
        a=p.sum(); b=q.sum(); s=(1-mu)*a+(1+mu)*b
        M=np.zeros((4,5),complex); M[0,0]=s/2; M[1,0]=s/2; M[2,0]=-a-(1+mu)*b; M[2,1:]=p; M[3,0]=(mu-1)*a-b; M[3,1:]=q; B.append(M)
    return np.array(B)
def check(B,rg,npts=30):
    e=0
    for _ in range(npts):
        c=rg.normal(size=len(B))+1j*rg.normal(size=len(B)); Y=np.tensordot(c,B,axes=1)
        e=max(e,abs(G(1+Y).sum()-120),abs(G(Y)).max())
    return e
def crit(mu,Y0,rg,tol=1e-8):
    """dim Omega from the reduced criterion: 1 + dim{v : s*gamma_v in D_0}, D_0 spanned by the 15 generators, as functions on Y_0."""
    P=np.array([y[0] for y in Y0]); Q=np.array([y[1] for y in Y0]); pts=rg.normal(size=(60,4))+1j*rg.normal(size=(60,4))
    p=pts@P; q=pts@Q; a=p.sum(1); b=q.sum(1); s=(1-mu)*a+(1+mu)*b; p0=-a-(1+mu)*b; q0=(mu-1)*a-b
    Pp=1+p; Qq=1+q; P0=1+p0; Q0=1+q0
    al=Pp.sum(1); be=Qq.sum(1); gam=al*be-(Pp*Qq).sum(1)
    alj=al[:,None]-Pp; bej=be[:,None]-Qq; gj=alj*bej-((Pp*Qq).sum(1)[:,None]-Pp*Qq); hj=2*P0[:,None]*bej+2*Q0[:,None]*alj
    gens=[gam,be,al]+[(2+s/2)*gj[:,j]+hj[:,j] for j in range(4)]+[(3+s)*bej[:,j]+3*Q0 for j in range(4)]+[(3+s)*alj[:,j]+3*P0 for j in range(4)]
    MD=np.array(gens).T; Mv=s[:,None]*gj
    r=lambda M: int((np.linalg.svd(M,compute_uv=False)>tol*np.linalg.svd(M,compute_uv=False)[0]).sum())
    return 5-(r(np.hstack([Mv,MD]))-r(MD)), r(MD)
if __name__=='__main__':
    rg=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 1)
    cn=lambda *sh: rg.normal(size=sh)+1j*rg.normal(size=sh)
    def run(name,mu,Ap,W):
        Y0=buildY0(np.array(Ap,complex),np.array(W,complex)); B=buildX(mu,Y0)
        rows=[rk(B[:,i,:]) for i in range(4)]; cols=[rk(B[:,:,j]) for j in range(5)]
        print('%-34s dim X=%d level/top err %.1e rows %s cols %s  criterion: dim Omega=%d (dim D_0=%d)'%((name,rk(B.reshape(len(B),-1)),check(B,rg),rows,cols)+crit(mu,Y0,rg)),flush=True)
        report('   T_1 tool:',B)
    # S2: k=2 split, mu random
    Ap=cn(2,4); run('S2 random, mu random',cn(),Ap,np.zeros((2,2)))
    Ap=cn(2,4); run('S2 random, mu=0',0,Ap,np.zeros((2,2)))
    # S3s: k=3 split, mu=-1
    n=cn(4); Ap=np.linalg.svd(n[None,:])[2][1:].conj(); run('S3s random n, mu=-1',-1,Ap,np.zeros((3,3)))
    n=np.array([2,2,2,5.0]); Ap=np.linalg.svd(n[None,:])[2][1:].conj(); run('S3s n=(2,2,2,5), mu=-1',-1,Ap,np.zeros((3,3)))
    n=np.array([2,2,5,5.0]); Ap=np.linalg.svd(n[None,:])[2][1:].conj(); run('S3s n=(2,2,5,5), mu=-1',-1,Ap,np.zeros((3,3)))
    n=cn(4); Ap=np.linalg.svd(n[None,:])[2][1:].conj(); run('S3s random n, mu random (iii fails)',cn(),Ap,np.zeros((3,3)))
    # S1: k=1 split, mu=1
    Ap=cn(1,4); run('S1 random, mu=1',1,Ap,np.zeros((1,1)))
    Ap=np.array([[2,2,2,5.0]]); run('S1 alpha=(2,2,2,5), mu=1',1,Ap,np.zeros((1,1)))
    # S3n: k=3 non-split
    n=cn(4); Ap=np.linalg.svd(n[None,:])[2][1:].conj(); W=cn(3,3); W=W-W.T; run('S3n random (iii not imposed)',cn(),Ap,W)
