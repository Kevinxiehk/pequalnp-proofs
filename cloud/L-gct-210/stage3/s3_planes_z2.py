import numpy as np, itertools, time, sys
from scipy.optimize import least_squares
# (S3), z_e = 2, WEAKENED plane problem (section 22 (e) / 24): planes P_0..P_3 (rows a..d), Z (index 4); marked vectors p_kl in P_k (l != k).
#   (Q4R)  P_a P_b P_c P_d = 0 in A_4.
#   for every triple {k,l,m} of R (non-triangle normal form x = al x^{kl} + be x^{km} + ga x^{lm} of X_{re}):
#   (CZ6)  Z . p_kl p_lk P_m = 0  (and the two other pairs);      (CZc)  Z . (p_kl p_lm p_mk + p_km p_lk p_ml) = 0   in A_4.
#   hinges: marked vectors p_kl, p_km in P_k non-parallel; all ten triple products of the five planes nonzero; column condition.
P4=np.array(list(itertools.permutations(range(4)))); P3=np.array(list(itertools.permutations(range(3))))
R=range(4); K3=list(itertools.combinations(range(5),3)); TRI5=list(itertools.combinations(range(5),3)); TRI=list(itertools.combinations(R,3))
OTH={k:[l for l in R if l!=k] for k in R}
def unpack(x):
    z=x[:74]+1j*x[74:]
    A=z[:50].reshape(5,2,5); c=z[50:74].reshape(4,3,2)
    p=np.einsum('klb,kbj->klj',c,A[:4])                       # p[k][index of l in OTH[k]]
    return A,c,p
def mv(p,k,l): return p[k][OTH[k].index(l)]
def perm4rows(rows):                                         # rows: (n,4,5) -> (n,5) the five 4x4 subpermanents
    out=[]
    for m in range(5):
        cols=[c for c in range(5) if c!=m]; X=rows[:,:,cols]
        out.append(sum(X[:,0,q[0]]*X[:,1,q[1]]*X[:,2,q[2]]*X[:,3,q[3]] for q in P4))
    return np.stack(out,axis=1)
# vector table: 0..9 = plane basis vectors (plane i, basis e -> 2*i+e); 10..21 = marked vectors p[k][t] -> 10+3*k+t
def vid_pl(i,e): return 2*i+e
def vid_mv(k,l): return 10+3*k+OTH[k].index(l)
I_Q=[[vid_pl(i,eps[i]) for i in R] for eps in itertools.product(range(2),repeat=4)]
I_6=[]; I_C1=[]; I_C2=[]
for (k,l,m) in TRI:
    for (i,j,o) in ((k,l,m),(k,m,l),(l,m,k)):
        for zz in range(2):
            for e in range(2): I_6.append([vid_pl(4,zz),vid_mv(i,j),vid_mv(j,i),vid_pl(o,e)])
    for zz in range(2):
        I_C1.append([vid_pl(4,zz),vid_mv(k,l),vid_mv(l,m),vid_mv(m,k)]); I_C2.append([vid_pl(4,zz),vid_mv(k,m),vid_mv(l,k),vid_mv(m,l)])
I_Q=np.array(I_Q); I_6=np.array(I_6); I_C1=np.array(I_C1); I_C2=np.array(I_C2)
def conds(A,p):
    V=np.concatenate([A.reshape(10,5),p.reshape(12,5)])
    return perm4rows(V[I_Q]).ravel(), perm4rows(V[I_6]).ravel(), (perm4rows(V[I_C1])+perm4rows(V[I_C2])).ravel()
ti=[];te=[];tc=[]
for T in TRI5:
    for eps in itertools.product(range(2),repeat=3):
        for K in K3: ti.append(T); te.append(eps); tc.append(K)
TI=np.array(ti); TE=np.array(te); TC=np.array(tc)
def trip(A):
    Mx=A[TI[:,:,None],TE[:,:,None],TC[:,None,:]]
    v=sum(Mx[:,0,q[0]]*Mx[:,1,q[1]]*Mx[:,2,q[2]] for q in P3)
    return np.sqrt((np.abs(v.reshape(10,80))**2).sum(1))
DELTA=float(sys.argv[2]); NVAN=int(sys.argv[3]); CMIN=0.35
def res(x,wt=3.0):
    A,c,p=unpack(x); q4r,cz6,czc=conds(A,p)
    G=(np.einsum('iaj,ibj->iab',A,A.conj())-np.eye(2)[None]).ravel()
    nc=(np.abs(c)**2).sum(2).ravel()-1
    dets=np.array([abs(c[k][i][0]*c[k][j][1]-c[k][i][1]*c[k][j][0]) for k in R for (i,j) in ((0,1),(0,2),(1,2))])
    h0=wt*np.maximum(0,0.3-dets); h1=wt*np.maximum(0,DELTA-trip(A))
    cn=np.sort(np.sqrt((np.abs(A)**2).sum(axis=(0,1)))); h2=wt*np.maximum(0,CMIN-cn[NVAN:])
    r=np.concatenate([q4r,cz6,czc,G]); return np.concatenate([r.real,r.imag,nc,h0,h1,h2])
def rank(M,tol=1e-6):
    s=np.linalg.svd(np.atleast_2d(M),compute_uv=False); return int((s>tol*max(1,s[0])).sum())
if __name__=='__main__':
    rng=np.random.default_rng(int(sys.argv[1])); TL=float(sys.argv[4]); t0=time.time(); best=[]; kinds={}; sols=[]
    x0=rng.normal(size=148)*0.6; t1=time.time(); res(x0); print('eval %.4f s'%(time.time()-t1),flush=True)
    for s in range(1000):
        if time.time()-t0>TL: break
        sol=least_squares(res,rng.normal(size=148)*0.6,method='lm',max_nfev=int(sys.argv[5]))
        cst=np.sqrt(2*sol.cost); best.append(cst)
        if cst<1e-8:
            A,c,p=unpack(sol.x); sols.append(sol.x)
            cn=np.sqrt((np.abs(A)**2).sum(axis=(0,1))); ncol=int((cn>1e-5).sum())
            full=[]                                          # does the FULL (Q4) hold for the 4-sets containing Z ?
            for (k,l,m) in TRI:
                L=[[A[4][zz],A[k][e1],A[l][e2],A[m][e3]] for zz in range(2) for e1 in range(2) for e2 in range(2) for e3 in range(2)]
                full.append(np.abs(perm4rows(np.array(L))).max()<1e-6)
            coord=[tuple(np.nonzero(np.linalg.norm(A[i],axis=0)>1e-5)[0]) for i in range(5)]
            ncoord=max([sum(1 for t in coord if t==u) for u in set(coord) if len(u)==2],default=0)
            key=('cols %d'%ncol,'full Q4 for the 4 sets with Z: %d of 4'%sum(full),'max #planes equal to one coordinate plane: %d'%ncoord,'dim sum of the 5 planes %d'%rank(A.reshape(10,5)))
            kinds[key]=kinds.get(key,0)+1
    print('NVAN',NVAN,'DELTA',DELTA,': starts %d, exact solutions %d  (%.0f s)'%(s,len(sols),time.time()-t0))
    if best: print('residual quantiles (min, 10%%, median): %.2e %.2e %.2e'%(min(best),np.quantile(best,0.1),np.median(best)))
    for k,v in sorted(kinds.items(),key=lambda t:-t[1]): print('  ',v,k)
    np.save('s3_planes_z2_sols_%s_v%d.npy'%(sys.argv[1],NVAN),np.array(sols))
