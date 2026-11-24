# Case "exactly two minimal pairs (1,2),(1,3)", lam_23 = 3, X_123 = 0: I_3^perp = N_12 + N_13 + C n**, n** on rows 2,3.
# Necessary: row-1 components of the two pair relations agree mod 1 (else dim count contradiction).
# For each S with f_1,f_2,f_3,g_12,g_13 independent on C^{3xS}: n**|K_S = 0 or n**|K_S divides the cubic perm^u|K_S.
# Numerical (float) survey: is there any admissible n** (nonzero on K = ker of the five functionals)?
import sys, itertools, numpy as np; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
from pairlib import nullspace, rank, perm
rng=np.random.default_rng(12)
def rnd(*k): return rng.normal(size=k)+1j*rng.normal(size=k)
def struct(kind,data,eps=None):
    # returns w (kappa^i'/kappa^i up to scalar), A_first, A_second
    if kind=='I':
        C=np.array(data,float); return np.where(C>0,1,-1).astype(complex),C,-C
    cells=np.array(data); w=np.where(cells==0,eps*1j,np.where(cells==1,1,-1)).astype(complex)
    return w,(cells==2).astype(float),(cells==1).astype(float)
def all_structs():
    out=[]
    for e in itertools.product([1,0],repeat=5):
        if e[0]!=1 or sum(e)==5: continue
        out.append(('I',e,None))
    for cells in itertools.product(range(3),repeat=5):
        if len(set(cells))<3: continue
        for eps in (1,-1): out.append(('II',cells,eps))
    return out
def canon():
    out=[('I',(1,0,0,0,0),None),('I',(1,1,0,0,0),None)]
    for comp in ((1,1,3),(1,3,1),(3,1,1),(1,2,2),(2,1,2),(2,2,1)):
        out.append(('II',tuple([0]*comp[0]+[1]*comp[1]+[2]*comp[2]),1))
    return out
def linfactors(cfun):
    # linear factors of a cubic form on C^4 (numerically): planes through one root on each of 3 random lines
    lines=[(rnd(4),rnd(4)) for _ in range(3)]; pts=[]
    for p,d in lines:
        ss=np.array([0,1,2,3]); vals=np.array([cfun(p+s*d) for s in ss]); co=np.polyfit(ss,vals,3)
        if np.abs(co).max()<1e-9: return None   # cubic identically zero (generic line)
        rts=np.roots(co); pts.append([p+s*d for s in rts])
    facs=[]
    for a in pts[0]:
        for b in pts[1]:
            for c in pts[2]:
                n=nullspace(np.array([a,b,c]))          # vectors n with a.n=b.n=c.n=0 (bilinear)
                if n.shape[1]!=1: continue
                lam=n[:,0].conj()                       # nullspace returns conj-orthogonal; want a@lam=0 bilinear
                lam=np.linalg.svd(np.array([a,b,c]))[2][-1].conj()
                H=nullspace(lam[None,:].conj()) if False else None
                # basis of hyperplane {v: lam.v = 0}
                Hb=np.linalg.svd(lam[None,:])[2][1:].conj().T
                if np.abs(lam@Hb).max()>1e-8: continue
                ok=all(abs(cfun(Hb@rnd(3)))<1e-7 for _ in range(4))
                if ok and not any(rank(np.array([lam,f]))==1 for f in facs): facs.append(lam)
    return facs
def analyse(s12,s13):
    w2,A1,A2=struct(*s12); w3,B1,B3=struct(*s13)
    if np.abs(A1-B1).max()<1e-9: sg=-1
    elif np.abs(A1+B1-1).max()<1e-9: sg=+1
    else: return 'dimcount'
    one=np.ones(5)
    def F(rows):
        v=np.zeros((3,5),complex)
        for i,vec in rows: v[i]=vec
        return v.reshape(-1)
    Fs=np.array([F([(0,one)]),F([(1,one)]),F([(2,one)]),F([(0,A1),(1,A2)]),F([(0,B1),(2,B3)])])
    K=nullspace(Fs)                                # 15 x 10 basis of K (columns)
    # W0: functionals (0,m2,m3) restricted to K  -> coordinates nu = m @ K ; W0 = row space of M0 = [e_k for k in rows 2,3] @ K
    M0=np.eye(15)[5:]@K                            # 10 x 10
    W0=nullspace(nullspace(M0.T.conj()).T.conj()) if False else None
    # represent nu by m in C^10 (rows 2,3): nu = m @ M0. Unknown m; trivial m: those with m@M0 = 0.
    u=np.array([one,1/w2,1/w3])
    cons=[]   # list of (KS_in_K coords (10 x 4), factors list or None)
    for S in itertools.combinations(range(5),3):
        Sc=[c for c in range(5) if c not in S]
        if rank(Fs[:,[i*5+c for i in range(3) for c in S]])<5: continue
        rows=[i*5+c for i in range(3) for c in Sc]
        E=nullspace(K[rows,:])                     # coords in K of K_S (10 x 4)
        if E.shape[1]!=4: continue
        def cfun(v,E=E,S=S): 
            tau=(K@(E@v)).reshape(3,5); return perm((tau*u)[:,list(S)])
        facs=linfactors(cfun)
        if facs is None: continue                  # cubic == 0 on K_S: no constraint
        cons.append((M0@E,facs))                   # m -> restriction to K_S: m @ (M0 E)  (4-vector)
    # DFS over choices: subspace V of m (10-dim) ; choice 0: m@R = 0 ; choice k: m@R parallel to fac_k
    triv=nullspace(M0.T)                           # m with m@M0=0  (as column vectors: M0^T m = 0)
    sols=[]
    R1=np.eye(15)[:5]@K                            # row-1 functionals restricted to K (5 x 10); a nu in their span is
    r1=rank(R1)                                    # impossible too (I_3^perp has no one-row element since pi_1(L^)=C^5)
    def dfs(idx,V):
        # V: basis (10 x d) of current subspace of m
        if V.shape[1]==0 or rank(np.vstack([R1,(M0.T@V).T]))==r1: return   # only trivial / row-1 functionals left
        if idx==len(cons): sols.append(V); return
        R,facs=cons[idx]
        # choice 0
        A=(R.T@V); 
        V0=V@nullspace(A); dfs(idx+1,V0)
        for lam in facs:
            # m@R in C lam  <=> (m@R)@P = 0 where P = basis of vectors orthogonal (bilinear) to ... need projector killing lam
            Pk=np.linalg.svd(lam[None,:])[2][1:].conj().T   # 4x3: columns c with lam.c = 0 ... (bilinear: lam@c=0)
            Pk=Pk if np.abs(lam@Pk).max()<1e-9 else nullspace(lam[None,:])
            A=(Pk.T@R.T@V); Vk=V@nullspace(A)
            dfs(idx+1,Vk)
    dfs(0,np.eye(10,dtype=complex))
    return ('SURVIVES',len(cons),len(sols),max(rank(np.vstack([R1,(M0.T@V).T]))-r1 for V in sols)) if sols else ('killed',len(cons))
if __name__=='__main__':
    stats={}; surv=[]
    for s12 in canon():
        for s13 in all_structs():
            r=analyse(s12,s13); key=(s12[0],s13[0],r if isinstance(r,str) else r[0])
            stats[key]=stats.get(key,0)+1
            if not isinstance(r,str) and r[0]=='SURVIVES': surv.append((s12,s13,r))
    for k,v in sorted(stats.items()): print(k,v)
    print('survivors:',len(surv)); [print('  ',s) for s in surv[:40]]
