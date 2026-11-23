# verify2 round 5: reg2's exact family M*(x,y) (NOTES-reg2 RESULT B): level? full free row? dim T_1, Omega, FO2 bound (own code, fo2lib).
import numpy as np, sys, itertools
sys.path.insert(0,'/home/claude/work/L-gct-210/verify2')
import fo2lib
from fractions import Fraction as Fr
def Mstar(x,y):
    B=[]
    for w in ([1,-1,-1,1,0],[1,0,0,0,-1],[0,1,1,-2,0]):            # {w : sum w = 0, w_1 = w_2}: 3-dim
        t=np.zeros((4,5),complex); t[3]=w; B.append(t)
    t=np.zeros((4,5),complex); t[:3,0]=x; B.append(t)
    t=np.zeros((4,5),complex); t[:3,3]=y; B.append(t)
    t=np.zeros((4,5),complex); t[2,1]=1; t[2,2]=-1; B.append(t)
    return np.array(B)
P4=list(itertools.permutations(range(4)))
def F45(Y):
    return sum(np.prod([Y[i,f[i]] for i in range(4)]) for f in itertools.permutations(range(5),4))
rng=np.random.default_rng(1)
for x,y in (((1,-1,0),(1,1,-2)),((2,-3,1),(1,1,1)),((1,1j,-1-1j),(1,-1j,-1+1j))):
    x=np.array(x,complex); y=np.array(y,complex)
    if abs(x.sum())>1e-12 or abs(y.sum())>1e-12 or abs(x@y)>1e-12: print('parameters',x,y,'do not satisfy sum x = sum y = <x,y> = 0: skipped'); continue
    B4=Mstar(x,y); d=len(B4)
    lev=max(abs(F45(1+np.tensordot(rng.normal(size=d)+1j*rng.normal(size=d),B4,axes=1))-120) for _ in range(8))
    B=np.zeros((d,5,5),complex); B[:,:4,:]=B4
    J=np.ones((5,5))
    def pt():
        c=rng.normal(size=d)+1j*rng.normal(size=d); return J+np.tensordot(c,B,axes=1)
    A=np.array([fo2lib.cof(pt()) for _ in range(80)]); u,s,vh=np.linalg.svd(A); r=int(np.sum(s>1e-9*s[0])); N=vh[r:].conj().T
    Q=sum((rng.normal()+1j*rng.normal())*fo2lib.hess(pt()) for _ in range(6)); sg=np.linalg.svd(N.T@Q@N,compute_uv=False); rq=int(np.sum(sg>1e-8*sg[0]))
    Om=N.reshape(5,5,-1)[4]; so=np.linalg.svd(Om,compute_uv=False); ro=int(np.sum(so>1e-8*so[0]))
    # Omega^perp
    uu,ss,vv=np.linalg.svd(Om.T); ann=vv[ro:].conj()
    # single-row parts
    zr=[]
    for i in range(4):
        idx=[5*k+j for k in range(4) for j in range(5) if k!=i]; Mx=B4.reshape(d,20)[:,idx]
        zr.append(d-np.linalg.matrix_rank(Mx,tol=1e-9))
    # 4x4 subpermanents of Y itself (Phi)
    phi=0
    for _ in range(6):
        Y=np.tensordot(rng.normal(size=d)+1j*rng.normal(size=d),B4,axes=1)
        phi=max(phi,max(abs(sum(np.prod([np.delete(Y,j,axis=1)[i,p[i]] for i in range(4)]) for p in P4)) for j in range(5)))
    print('M*(x,y), x = %s, y = %s: dim %d, level err %.1e, single-row parts %s, max |Phi| %.1e'%(np.round(x,2),np.round(y,2),np.linalg.matrix_rank(B4.reshape(d,20)),lev,zr,phi))
    print('    dim T_1 = %d (sv %.1e | %.1e), dim Omega = %d, Omega^perp spanned by %s, rank q = %d, FO2 bound = %d'%(N.shape[1],s[r-1]/s[0],s[r]/s[0] if r<len(s) else 0,ro,np.round(ann/np.abs(ann).max(),3),rq,N.shape[1]-(rq+1)//2))
