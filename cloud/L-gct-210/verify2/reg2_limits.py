# verify2 round 4: the near-degenerate (6,3) files: round the reduced basis to its sparse limit and recompute level error, T_1, FO2, Omega.
import numpy as np, sys, itertools
sys.path.insert(0,'/home/claude/work/L-gct-210/verify2')
import fo2lib
J=np.ones((5,5))
def perm5(A): return sum(np.prod([A[i,p[i]] for i in range(5)]) for p in itertools.permutations(range(5)))
def rref(A,tol=1e-6):
    A=A.copy(); r=0; piv=[]
    for c in range(A.shape[1]):
        p=r+np.argmax(np.abs(A[r:,c]))
        if abs(A[p,c])<tol: continue
        A[[r,p]]=A[[p,r]]; A[r]/=A[r,c]
        for i in range(len(A)):
            if i!=r: A[i]-=A[i,c]*A[r]
        piv.append(c); r+=1
        if r==len(A): break
    return A,piv
rng=np.random.default_rng(5)
for name in [a for a in sys.argv[1:] if not a.startswith('--')]:
    B4=np.asarray(np.load('/home/claude/work/L-gct-210/rows/%s.npy'%name),dtype=complex); d=len(B4)
    R,piv=rref(B4.reshape(d,20))
    small=np.abs(R)<1e-5; nsmall=int(np.sum(small&(np.abs(R)>1e-13)))
    R2=R.copy(); R2[small]=0
    # round entries close to small rationals
    def rr(z):
        for den in (1,2,3,4,5,6):
            w=np.round(z*den)/den
            if abs(w-z)<1e-5: return w
        return z
    R3=R2 if '--zero-only' in sys.argv else np.array([[rr(z) for z in row] for row in R2])
    for tag,RR in (('raw',R),('rounded',R3)):
        B=np.zeros((d,5,5),complex); B[:,:4,:]=RR.reshape(d,4,5)
        err=0
        for _ in range(8):
            c=rng.normal(size=d)+1j*rng.normal(size=d); c/=np.linalg.norm(c); err=max(err,abs(perm5(J+np.tensordot(c,B,axes=1))-120))
        res=[]
        for tol in (1e-9,):
            def pt():
                c=rng.normal(size=d)+1j*rng.normal(size=d); return J+np.tensordot(c,B,axes=1)
            A=np.array([fo2lib.cof(pt()) for _ in range(60)])
            u,s,vh=np.linalg.svd(A); r=int(np.sum(s>tol*s[0])); N=vh[r:].conj().T
            Q=sum((rng.normal()+1j*rng.normal())*fo2lib.hess(pt()) for _ in range(5))
            if N.shape[1]==0: res=(0,0,0,0,0.0); continue
            sg=np.linalg.svd(N.T@Q@N,compute_uv=False); rq=int(np.sum(sg>1e-7*max(1,sg[0])))
            so=np.linalg.svd(N.reshape(5,5,-1)[4],compute_uv=False); ro=int(np.sum(so>1e-7*max(1,so[0])))
            res=(N.shape[1],rq,N.shape[1]-(rq+1)//2,ro,s[r-1]/s[0])
        print('%-22s %-8s level err %.1e | T_1 %2d rank %d bound %d Omega %d (smallest kept sv %.0e)'%(name,tag,err,*res), ('| entries rounded to 0: %d, nonzero entries left: %d, non-rational entries: %d'%(nsmall,int(np.sum(np.abs(R3)>0)),int(np.sum((np.abs(R3)>0)&(np.abs(R3-np.round(R3*60)/60)>1e-9)))) if tag=='rounded' else ''),flush=True)
