import numpy as np, itertools, time, sys
from scipy.optimize import least_squares
# (S3), z_e = 1, plane problem: four 2-planes P_0..P_3 = P_a..P_d (2x5, orthonormal rows) and a unit vector w with
#   (Q4R) P_a P_b P_c P_d = 0 in A_4;   (CZ) w P_k P_l P_m = 0 in A_4 for the four triples;
#   hinges: the four triple products P_k P_l P_m have norm >= DELTA; all but NVAN columns have norm >= 0.35.
P4=np.array(list(itertools.permutations(range(4)))); P3=np.array(list(itertools.permutations(range(3))))
TRI=list(itertools.combinations(range(4),3)); K3=list(itertools.combinations(range(5),3))
ri=[];re=[];co=[]
for eps in itertools.product(range(2),repeat=4):
    for m in range(5): ri.append((0,1,2,3)); re.append(eps); co.append([c for c in range(5) if c!=m])
for T in TRI:
    for eps in itertools.product(range(2),repeat=3):
        for m in range(5): ri.append((4,)+T); re.append((0,)+eps); co.append([c for c in range(5) if c!=m])
RI=np.array(ri); RE=np.array(re); CO=np.array(co)
ti=[];te=[];tc=[]
for T in TRI:
    for eps in itertools.product(range(2),repeat=3):
        for K in K3: ti.append(T); te.append(eps); tc.append(K)
TI=np.array(ti); TE=np.array(te); TC=np.array(tc)
def unpack(x):
    z=x[:45]+1j*x[45:]; A=np.zeros((5,2,5),complex); A[:4]=z[:40].reshape(4,2,5); A[4,0]=z[40:45]; return A
def q4(A):
    Mx=A[RI[:,:,None],RE[:,:,None],CO[:,None,:]]
    return sum(Mx[:,0,p[0]]*Mx[:,1,p[1]]*Mx[:,2,p[2]]*Mx[:,3,p[3]] for p in P4)
def trip(A):
    Mx=A[TI[:,:,None],TE[:,:,None],TC[:,None,:]]
    v=sum(Mx[:,0,p[0]]*Mx[:,1,p[1]]*Mx[:,2,p[2]] for p in P3)
    return np.sqrt((np.abs(v.reshape(4,80))**2).sum(1))
DELTA=float(sys.argv[2]); NVAN=int(sys.argv[3]); CMIN=0.35
def res(x,wt=3.0):
    A=unpack(x); r=q4(A)
    G=np.einsum('iaj,ibj->iab',A[:4],A[:4].conj())-np.eye(2)[None]
    nw=np.array([np.vdot(A[4,0],A[4,0])-1])
    hinge=wt*np.maximum(0,DELTA-trip(A))
    cn=np.sort(np.sqrt((np.abs(A[:4])**2).sum(axis=(0,1)))); h2=wt*np.maximum(0,CMIN-cn[NVAN:])
    aw=np.sort(np.abs(A[4,0]))[::-1]; h3=np.array([wt*max(0,0.3-aw[1])])      # w is not (near) a unit vector
    return np.concatenate([r.real,r.imag,G.real.ravel(),G.imag.ravel(),nw.real,hinge,h2,h3])
def rank(M,tol=1e-6):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol*max(1,s[0])).sum())
rng=np.random.default_rng(int(sys.argv[1])); TL=float(sys.argv[4]); t0=time.time(); best=[]; kinds={}; sols=[]
for s in range(1000):
    if time.time()-t0>TL: break
    sol=least_squares(res,rng.normal(size=90)*0.6,method='lm',max_nfev=int(sys.argv[5]))
    c=np.sqrt(2*sol.cost); best.append(c)
    if c<1e-8:
        A=unpack(sol.x); sols.append(sol.x); w=A[4,0]
        cn=np.sqrt((np.abs(A[:4])**2).sum(axis=(0,1))); ncol=int((cn>1e-5).sum())
        sw=int((np.abs(w)>1e-5).sum()); inpl=sum(1 for i in range(4) if rank(np.vstack([A[i],w[None]]))==2)
        dall=rank(A[:4].reshape(8,5)); meet=sum(1 for i in range(4) for k in range(i) if rank(np.vstack([A[i],A[k]]))<4)
        eq=sum(1 for i in range(4) for k in range(i) if rank(np.vstack([A[i],A[k]]))==2)
        key=('cols (planes) %d'%ncol,'cols (planes and w) %d'%int((np.sqrt((np.abs(A)**2).sum(axis=(0,1)))>1e-5).sum()),'max #planes equal to one coordinate plane %d'%max([sum(1 for i in range(4) if tuple(np.nonzero(np.linalg.norm(A[i],axis=0)>1e-5)[0])==u) for u in set(tuple(np.nonzero(np.linalg.norm(A[i],axis=0)>1e-5)[0]) for i in range(4)) if len(u)==2],default=0),'|supp w| %d'%sw,'#planes containing w: %d'%inpl,'dim sum of planes %d'%dall,'#meeting pairs %d'%meet,'#equal pairs %d'%eq)
        kinds[key]=kinds.get(key,0)+1
print('NVAN',NVAN,'DELTA',DELTA,': starts %d, exact solutions %d  (%.0f s)'%(s,len(sols),time.time()-t0))
if best: print('residual quantiles (min, 10%%, median): %.2e %.2e %.2e'%(min(best),np.quantile(best,0.1),np.median(best)))
for k,v in sorted(kinds.items(),key=lambda t:-t[1]): print('  ',v,k)
np.save('s3_planes_lineW_sols_%s_v%d.npy'%(sys.argv[1],NVAN),np.array(sols))
