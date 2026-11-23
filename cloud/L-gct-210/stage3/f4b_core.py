import numpy as np, itertools, sys, time
from scipy.optimize import least_squares
# Round 7: family F4b, SYSTEM A (7-dim core) and SYSTEM B (core + two free matrices), see COMPUTE-stage3.md item 3.
# vectors (index): y_a..y_d = 0..3, p = 4, w = 5, g_a..g_d = 6..9   (rows a,b,c,d,e = 0..4)
SG=np.array(list(itertools.product([1,-1],repeat=4))); SG=np.concatenate([np.ones((16,1)),SG],axis=1); SP=SG.prod(axis=1)
def perm5(X):                      # Glynn, X (N,5,5)
    S=np.einsum('di,nij->ndj',SG,X); return (S.prod(axis=2)*SP).sum(axis=1)/16.0
MODE=sys.argv[2]; NEX=2 if MODE=='B' else 0; D=7+NEX
NV=10; NU=NV*5+NEX*25
def basis(z):
    v=z[:50].reshape(10,5); B=np.zeros((D,5,5),dtype=complex)
    for r in range(4): B[r,r]=v[r]; B[r,4]=v[4]
    B[4,4]=v[5]; B[5,0]=v[6]; B[5,1]=v[7]; B[6,2]=v[8]; B[6,3]=v[9]
    if NEX: B[7:]=z[50:].reshape(NEX,5,5)
    return v,B
rgc=np.random.default_rng(12345); NP=900 if MODE=='A' else 2200
C=(rgc.normal(size=(NP,D))+1j*rgc.normal(size=(NP,D)))*0.6
HING=int(sys.argv[3]); WT=3.0
def sv2(u,v):
    A=np.array([u/np.linalg.norm(u),v/np.linalg.norm(v)]); return np.linalg.svd(A,compute_uv=False)[1]
def res(x):
    z=x[:NU]+1j*x[NU:]; v,B=basis(z)
    X=np.ones((5,5))+np.tensordot(C,B,axes=1); r=(perm5(X)-120.0)/30.0
    nr=np.sqrt((np.abs(v)**2).sum(axis=1))
    out=[r.real,r.imag,[ (nr[:5]**2).sum()-5, nr[5]-1, nr[6]**2+nr[7]**2-2, nr[8]**2+nr[9]**2-2 ]]
    if HING:
        h=[WT*max(0,0.3-nr[i]) for i in range(10)]
        h+=[WT*max(0,0.3-sv2(v[r],v[6+r])) for r in range(4)]+[WT*max(0,0.3-sv2(v[4],v[5]))]
        out.append(h)
    if NEX:
        T=B[7:].reshape(NEX,25); G=T@T.conj().T-np.eye(NEX); out+= [G.real.ravel(),G.imag.ravel()]
        if HING:       # t_i away from M: distance of t_i to span(M) >= 0.5 ; all a_r = 1 for L
            Mb=B[:7].reshape(7,25); Q,_=np.linalg.qr(Mb.T); Tp=T-(T@Q.conj())@Q.T
            s=np.linalg.svd(Tp,compute_uv=False); out.append([WT*max(0,0.5-s[-1])])
            for r in range(5):
                s=np.linalg.svd(B[:,r,:],compute_uv=False); out.append([WT*max(0,0.2-s[3])])
    return np.concatenate([np.ravel(o) for o in out])
def rank(M,tol=1e-6):
    s=np.linalg.svd(np.atleast_2d(M),compute_uv=False); return int((s>tol*max(1,s[0])).sum())
if __name__=='__main__':
    rng=np.random.default_rng(int(sys.argv[1])); TL=float(sys.argv[4]); t0=time.time(); best=[]; sols=[]
    x0=rng.normal(size=2*NU)*0.6; t1=time.time(); res(x0); print('eval %.4f s, unknowns %d'%(time.time()-t1,2*NU),flush=True)
    s=0
    while time.time()-t0<TL:
        s+=1
        sol=least_squares(res,rng.normal(size=2*NU)*0.6,method='lm',max_nfev=int(sys.argv[5]))
        cst=np.sqrt(2*sol.cost); best.append(cst)
        if cst<1e-8:
            z=sol.x[:NU]+1j*sol.x[NU:]; v,B=basis(z); sols.append(sol.x)
            nr=np.sqrt((np.abs(v)**2).sum(axis=1))
            print('SOL start %d cost %.1e  norms'%(s,cst),np.round(nr,2),' sv(y_r,g_r)',[round(sv2(v[r],v[6+r]),3) for r in range(4)],' sv(p,w) %.3f'%sv2(v[4],v[5]),
                  ' dim',rank(B.reshape(D,25)),' a_r',[5-rank(B[:,r,:]) for r in range(5)],' cols used',int((np.abs(v).max(axis=0)>1e-5).sum()),flush=True)
            np.set_printoptions(precision=3,suppress=True,linewidth=200); print(v)
    print('MODE',MODE,'HING',HING,': starts %d, solutions %d (%.0f s)'%(s,len(sols),time.time()-t0))
    if best: print('residual quantiles (min, 10%%, median): %.2e %.2e %.2e'%(min(best),np.quantile(best,0.1),np.median(best)))
    np.save('f4b_core_sols_%s_%s_%d.npy'%(sys.argv[1],MODE,HING),np.array(sols))
