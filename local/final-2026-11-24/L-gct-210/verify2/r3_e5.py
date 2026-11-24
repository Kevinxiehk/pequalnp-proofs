# verify2: independent check of stage2 R3-1 (E4)+(E5): for the 12 surviving exception configurations, collect the leaves V (linear families
# of candidate n** = (0,m_2,m_3)) of the (E2)-DFS, keep the maximal ones, and search inside each for an ADMISSIBLE m satisfying the FULL
# cube condition (perm_3 = k ell^3 on Pi_S = Pi~_S cap ker n** whenever ell != 0 there) for all ten S.  Claim: none exists.
import sys, itertools, importlib.util, numpy as np
from scipy.optimize import least_squares
spec=importlib.util.spec_from_file_location('r3s','/home/kevxhk/work/L-gct-210/stage2/r3_survey.py'); r3=importlib.util.module_from_spec(spec); spec.loader.exec_module(r3)
nullspace,rank,perm,typeII=r3.nullspace,r3.rank,r3.perm,r3.typeII
rng=np.random.default_rng(7)
def rnd(*k): return rng.normal(size=k)+1j*rng.normal(size=k)
def setup(s12,s13):
    w2,A1,A2,y12=typeII(*s12); w3,B1,B3,y13=typeII(*s13); one=np.ones(5)
    def F(rows):
        v=np.zeros((3,5),complex)
        for i,vec in rows: v[i]=vec
        return v.reshape(-1)
    A0=np.array([F([(0,one),(1,-one)]),F([(0,one),(2,-one)]),F([(0,A1+y12*one),(1,A2)]),F([(0,B1+y13*one),(2,B3)])])
    u=np.array([one,1/w2,1/w3]); cons=[]; full=[]
    for S in itertools.combinations(range(5),3):
        cols=[i*5+j for i in range(3) for j in S]
        Pt=nullspace(A0[:,cols]); ell=np.array([1,1,1,0,0,0,0,0,0])@Pt
        if np.abs(ell).max()<1e-9: continue
        Rt=np.zeros((10,Pt.shape[1]),complex)
        for k,j in enumerate(S): Rt[j]=Pt[3+k]; Rt[5+j]=Pt[6+k]
        full.append((S,Pt,ell,Rt))
        E=Pt@nullspace(ell[None,:]); d=E.shape[1]
        def cfun(v,E=E,S=S): return perm(((E@v).reshape(3,3))*u[:,list(S)])
        facs=r3.linfactors(cfun,d)
        if facs is None: continue
        R=np.zeros((10,d),complex)
        for k,j in enumerate(S): R[j]=E[3+k]; R[5+j]=E[6+k]
        cons.append((R,facs))
    def Bspace(vecs,which):
        Bm=np.zeros((10,7),complex); k=0
        for j in range(5): Bm[(0 if which==2 else 5)+j,k]=1; k+=1
        for v in vecs: Bm[(5 if which==2 else 0):(10 if which==2 else 5),k]=v; k+=1
        return Bm
    B12=Bspace([one,B3],2); B13=Bspace([one,A2],3)
    leaves=[]
    def dfs(idx,V):
        if V.shape[1]==0 or rank(np.hstack([B12,V]))==rank(B12) or rank(np.hstack([B13,V]))==rank(B13): return
        if idx==len(cons): leaves.append(V); return
        R,facs=cons[idx]
        dfs(idx+1,V@nullspace(R.T@V))
        for lam in facs:
            Pk=nullspace(lam[None,:]); dfs(idx+1,V@nullspace(Pk.T@R.T@V))
    dfs(0,np.eye(10,dtype=complex))
    # maximal leaves
    leaves.sort(key=lambda V:-V.shape[1]); mx=[]
    for V in leaves:
        if not any(rank(np.hstack([W,V]))==W.shape[1] for W in mx): mx.append(V)
    return u,full,B12,B13,mx
def cube_defect(m,u,full):
    """true test: max over S of the relative non-constancy of perm/ell^3 on Pi_S (0 if ell = 0 on Pi_S)"""
    worst=0
    for S,Pt,ell,Rt in full:
        n=m@Rt; N=nullspace(n[None,:]) if np.abs(n).max()>1e-9 else np.eye(Pt.shape[1],dtype=complex)
        l=ell@N
        if np.abs(l).max()<1e-7: continue
        vals=[]
        for _ in range(5):
            c=rnd(N.shape[1]); v=(Pt@(N@c)).reshape(3,3)*u[:,list(S)]; vals.append(perm(v)/(l@c)**3)
        worst=max(worst,max(abs(x-vals[0]) for x in vals)/max(1e-12,max(abs(x) for x in vals)))
    return worst
canon=[(0,1,2,2,2),(0,1,1,1,2),(0,0,0,1,2),(0,1,1,2,2),(0,0,1,2,2),(0,0,1,1,2)]
tot=0
for c12 in canon:
    s12=(c12,1)
    for cells in itertools.product(range(3),repeat=5):
        if len(set(cells))<3: continue
        for eps in (1,-1):
            rr=r3.analyse(s12,(cells,eps))
            if isinstance(rr,str) or rr[0]!='SURVIVES': continue
            tot+=1
            u,full,B12,B13,mx=setup(s12,(cells,eps))
            out=[]
            for V in mx:
                k=V.shape[1]; samples=[]
                for S,Pt,ell,Rt in full:
                    p=Pt.shape[1]; samples.append((S,Pt,ell,Rt,rnd(p),[rnd(p) for _ in range(4)]))
                def res(z):
                    c=z[:k]+1j*z[k:]; m=V@c; r=[abs(np.vdot(c,c))-1]
                    for S,Pt,ell,Rt,e0,vs in samples:
                        n=m@Rt; pts=[(n@e0)*v-(n@v)*e0 for v in vs]
                        pv=[perm((Pt@x).reshape(3,3)*u[:,list(S)]) for x in pts]; lv=[ell@x for x in pts]
                        for a in range(1,4):
                            t=pv[0]*lv[a]**3-pv[a]*lv[0]**3; r+=[t.real,t.imag]
                    return np.array(r)
                best=[]; 
                for st in range(25):
                    sol=least_squares(res,rng.normal(size=2*k),method='lm',max_nfev=400)
                    if np.linalg.norm(sol.fun)<1e-9:
                        m=V@(sol.x[:k]+1j*sol.x[k:]); m=m/np.linalg.norm(m)
                        adm=min(np.linalg.svd(np.hstack([B12,m[:,None]]),compute_uv=False)[-1],np.linalg.svd(np.hstack([B13,m[:,None]]),compute_uv=False)[-1])
                        best.append((cube_defect(m,u,full),adm))
                nsol=len(best); true_adm=[b for b in best if b[0]<1e-6 and b[1]>1e-4]
                out.append((k,nsol,len(true_adm),max([b[1] for b in best],default=0)))
            print(c12,cells,eps,' maximal leaves: (dim, LM zeros of 25, of which TRUE cube solutions that are admissible, max admissibility among zeros):',out,flush=True)
print('surviving configurations treated:',tot)
