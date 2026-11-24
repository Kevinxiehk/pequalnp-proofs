# Extensions of a known level 4x5 space M_b (dim b) to 6-dim level spaces: any level M containing M_b lies in E_0(M_b), so
# M/M_b is a (6-b)-plane in E_0(M_b)/M_b.  LM over that Grassmannian (chart), residuals = level polynomial at sample points.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/chief')
import numpy as np, glob, itertools, time
from t import *
from a1 import embed, defect, phirank
from a5 import onb, rref_tol
from a6 import E0, T1
from a9 import Omega
PERM5=np.array(list(itertools.permutations(range(5))))
def perm5(A):          # A (N,5,5)
    return A[:,np.arange(5)[None,:],PERM5].prod(axis=2).sum(axis=1)
def F45(Y):            # Y (N,4,5): level polynomial sum over injections prod(1+Y)
    N=len(Y); A=np.ones((N,5,5),complex); A[:,:4,:]+=Y; return perm5(A)
def complement(M,E):
    Mb=M.reshape(len(M),20); Q,_=np.linalg.qr(Mb.T); Ev=E.reshape(len(E),20); X=Ev-(Ev@Q.conj())@Q.T
    u,s,vh=np.linalg.svd(X); r=int((s>1e-7).sum()); return vh[:r].reshape(r,4,5)
def solve_ext(M,D,m,rg,iters=200,N=320):
    b=len(M); q=len(D)
    # random unitary mixing of D for chart
    U,_=np.linalg.qr(rg.normal(size=(q,q))+1j*rg.normal(size=(q,q))); D=np.einsum('ab,bij->aij',U,D)
    C=rg.normal(size=(N,b))+1j*rg.normal(size=(N,b)); S=rg.normal(size=(N,m))+1j*rg.normal(size=(N,m))
    base=np.einsum('nk,kij->nij',C,M)
    def res(x):
        X=x.reshape(m,q-m); G=D[:m]+np.einsum('ab,bij->aij',X,D[m:])
        return F45(base+np.einsum('na,aij->nij',S,G))-120
    x=(rg.normal(size=m*(q-m))+1j*rg.normal(size=m*(q-m)))*0.7; mu=1e-2; r=res(x); c=np.linalg.norm(r)
    for it in range(iters):
        h=1e-6; J=np.empty((N,len(x)),complex)
        for a in range(len(x)):
            xp=x.copy(); xp[a]+=h; J[:,a]=(res(xp)-r)/h
        A=J.conj().T@J; g=J.conj().T@r
        for _ in range(8):
            dx=np.linalg.solve(A+mu*np.eye(len(x)),-g); rn=res(x+dx); cn=np.linalg.norm(rn)
            if cn<c: x=x+dx; r=rn; c=cn; mu=max(mu/5,1e-12); break
            mu*=6
        else: break
        if c<1e-11: break
    X=x.reshape(m,q-m); G=D[:m]+np.einsum('ab,bij->aij',X,D[m:])
    return c,np.concatenate([M,G],0)
def classify(B,rg):
    B=onb(B)
    def part(mask):
        A=B.reshape(len(B),-1)[:,~mask.ravel()].T; sv=np.linalg.svd(A,compute_uv=False); return int((sv<1e-4).sum())+max(0,len(B)-len(sv))
    sr=[]; sc=[]
    for i in range(4):
        mk=np.zeros((4,5),bool); mk[i]=True; sr.append(part(mk))
    for j in range(5):
        mk=np.zeros((4,5),bool); mk[:,j]=True; sc.append(part(mk))
    ds=defect(B,n=60); e=int((ds>1e-4*ds[0]).sum())
    T=T1(embed(B),rg,npts=90,tol=1e-5); nT=len(T); rho=T[:,4,:]; S=np.linalg.svd(rho,compute_uv=False); Om=[0]*int((S>1e-5*S[0]).sum())
    # neutral columns: defect vectors vanish in coordinate c
    rng=np.random.default_rng(7); from a1 import pk
    V=np.array([pk(np.einsum('k,kab->ab',rng.normal(size=len(B))+1j*rng.normal(size=len(B)),B),k) for _ in range(6) for k in (1,2,3,4)])
    nc=[c for c in range(5) if np.abs(V[:,c]).max()<1e-4*np.abs(V).max()]
    typ='F' if max(sr)==4 else ('NC' if (e==3 and len(Om)==2 and len(nc)==1) else 'OTHER')
    return typ,'srow %s scol %s e=%d Om=%d T1=%d neutral cols %s lev %.0e'%(sr,sc,e,len(Om),nT,nc,level_err(B))
if __name__=='__main__':
    import core
    def Lr(B,r):
        m=np.ones((5,5),bool); m[r]=False
        S=sub_supported(B,m); rows=[i for i in range(5) if i!=r]
        return S[:,rows,:]
    rg=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0); tmax=float(sys.argv[2]) if len(sys.argv)>2 else 100
    bases=[]
    for f in sorted(glob.glob('../rows/clm_p4_d5_*.npy')): bases.append((f.split('/')[-1],onb(np.load(f))))
    for name in ('ex1','ex2','ex3','fam2'):
        Bm=np.array([np.array(mm,dtype=complex) for mm in core.SP[name]()])
        for tr,Bt in (('row',Bm),('col',Bm.transpose(0,2,1))):
            for r in range(5):
                M=Lr(Bt,r)
                if len(M)==5: bases.append(('%s %s %d'%(name,tr,r),onb(M)))
    for f in sorted(glob.glob('../rows/clm_p4_d4_*.npy')): bases.append((f.split('/')[-1],onb(np.load(f))))
    t0=time.time()
    for name,M in bases:
        if time.time()-t0>tmax: print('time limit'); break
        E=E0(M,rg); D=complement(M,E); q=len(D); m=6-len(M)
        if q<m: print('%-28s dim %d E0 %d: no room'%(name,len(M),len(E))); continue
        if q==m:
            B=np.concatenate([M,D],0); le=level_err(onb(B)); print('%-28s dim %d E0 %d: E0 itself, level err %.1e %s'%(name,len(M),len(E),le,classify(B,rg) if le<1e-8 else '')); continue
        found={}
        for trial in range(6 if m==1 else 5):
            c,B=solve_ext(M,D,m,rg)
            if c<1e-9:
                typ,desc=classify(B,rg); found.setdefault(typ,[]).append(desc)
        print('%-28s dim %d E0 %d (q=%d,m=%d): found %s'%(name,len(M),len(E),q,m,{k:len(v) for k,v in found.items()}),flush=True)
        for k,v in found.items():
            for dsc in sorted(set(v))[:3]: print('      ',k,dsc)
