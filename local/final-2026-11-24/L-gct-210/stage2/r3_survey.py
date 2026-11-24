# Round 3: STRONGER necessary conditions for the exception triples (rows 1,2,3; (1,2),(1,3) minimal Type II; dim X_23 = 3;
# X_123 = 0).  I_3^perp = span(A0) + C n**, n** = (0,m_2,m_3).  For EVERY column triple S with ell != 0 on
# Pi~_S := span(A0)^perp cap C^{3xS} (constants y included), K_S := Pi~_S cap ker ell, c_S := perm|K_S (cubic):
#     n**|K_S = 0   or   n**|K_S is a linear factor of c_S            (ZBF + UFD, as in (T2)).
# Admissible m: m_3 not in span(1, 1_{Q_2'}) and m_2 not in span(1, 1_{Q_2})  (else I_12 or I_13 would get a third annihilator).
import sys, itertools, numpy as np; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
from pairlib import nullspace, rank, perm
rng=np.random.default_rng(41)
def rnd(*k): return rng.normal(size=k)+1j*rng.normal(size=k)
def typeII(cells,eps):
    cells=np.array(cells); w=np.where(cells==0,eps*1j,np.where(cells==1,1,-1)).astype(complex)
    return w,(cells==2).astype(float),(cells==1).astype(float),(-1+eps*1j)/2
def linfactors(cfun,d):
    lines=[(rnd(d),rnd(d)) for _ in range(d-1)]; pts=[]
    for p,dd in lines:
        ss=np.array([0,1,2,3]); vals=np.array([cfun(p+s*dd) for s in ss]); co=np.polyfit(ss,vals,3)
        if np.abs(co).max()<1e-9: return None
        pts.append([p+s*dd for s in np.roots(co)])
    facs=[]
    for combo in itertools.product(*pts):
        M=np.array(combo)                                 # (d-1) x d ; hyperplane {v: lam.v = 0} containing these points
        lam=np.linalg.svd(M)[2][-1].conj()
        if np.abs(M@lam).max()>1e-7: continue
        Hb=np.linalg.svd(lam[None,:])[2][1:].conj().T
        if all(abs(cfun(Hb@rnd(d-1)))<1e-7 for _ in range(4)) and not any(rank(np.array([lam,f]))==1 for f in facs): facs.append(lam)
    return facs
def analyse(s12,s13):
    w2,A1,A2,y12=typeII(*s12); w3,B1,B3,y13=typeII(*s13); one=np.ones(5)
    if not (np.abs(A1-B1).max()<1e-9 or np.abs(A1+B1-1).max()<1e-9): return 'dimcount'
    def F(rows):
        v=np.zeros((3,5),complex)
        for i,vec in rows: v[i]=vec
        return v.reshape(-1)
    A0=np.array([F([(0,one),(1,-one)]),F([(0,one),(2,-one)]),F([(0,A1+y12*one),(1,A2)]),F([(0,B1+y13*one),(2,B3)])])
    u=np.array([one,1/w2,1/w3]); cons=[]
    for S in itertools.combinations(range(5),3):
        cols=[i*5+j for i in range(3) for j in S]
        Pt=nullspace(A0[:,cols]); ell=np.array([1,1,1,0,0,0,0,0,0])@Pt
        if np.abs(ell).max()<1e-9: continue
        E=Pt@nullspace(ell[None,:]); d=E.shape[1]         # K_S basis (9 x d)
        def cfun(v,E=E,S=S): return perm(((E@v).reshape(3,3))*u[:,list(S)])
        facs=linfactors(cfun,d)
        if facs is None: continue
        R=np.zeros((10,d),complex)                        # m -> restriction to K_S
        for k,j in enumerate(S): R[j]=E[3+k]; R[5+j]=E[6+k]
        cons.append((R,facs))
    # admissibility
    def Bspace(vecs,which):
        Bm=np.zeros((10,7),complex); k=0
        for j in range(5):
            Bm[(0 if which==2 else 5)+j,k]=1; k+=1       # the unconstrained part
        for v in vecs:
            Bm[(5 if which==2 else 0):(10 if which==2 else 5),k]=v; k+=1
        return Bm
    B12=Bspace([one,B3],2); B13=Bspace([one,A2],3); r12=rank(B12); r13=rank(B13)
    sols=[]
    def dfs(idx,V):
        if V.shape[1]==0 or rank(np.hstack([B12,V]))==r12 or rank(np.hstack([B13,V]))==r13: return
        if idx==len(cons): sols.append(V.shape[1]); return
        R,facs=cons[idx]
        dfs(idx+1,V@nullspace(R.T@V))
        for lam in facs:
            Pk=np.linalg.svd(lam[None,:])[2][1:].conj().T
            if np.abs(lam@Pk).max()>1e-9: Pk=nullspace(lam[None,:])
            dfs(idx+1,V@nullspace(Pk.T@R.T@V))
    dfs(0,np.eye(10,dtype=complex))
    return ('SURVIVES',len(cons),len(sols),max(sols)) if sols else ('killed',len(cons))
if __name__=='__main__':
    stats={}; surv=[]
    for comp in ((1,1,3),(1,3,1),(3,1,1),(1,2,2),(2,1,2),(2,2,1)):
        s12=(tuple([0]*comp[0]+[1]*comp[1]+[2]*comp[2]),1)
        for cells in itertools.product(range(3),repeat=5):
            if len(set(cells))<3: continue
            for eps in (1,-1):
                r=analyse(s12,(cells,eps)); key=r if isinstance(r,str) else r[0]; stats[key]=stats.get(key,0)+1
                if key=='SURVIVES': surv.append((s12,(cells,eps),r))
    print(stats); print('survivors:',len(surv)); [print('  ',s) for s in surv]
