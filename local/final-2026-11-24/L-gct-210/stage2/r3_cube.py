# Round 3: FULL CUBE CONDITION for the surviving (II,II,lam=3) exception configurations (rows 1,2,3; (1,2),(1,3) minimal Type II,
# dim X_23 = 3, X_123 = 0).  I_3 = (N_12 + N_13)^perp cap ker n**,  n** = (0,m_2,m_3), m in a leaf space V of the necessary
# conditions (t8/r3_two_minimal).  Parameters: m = v + delta*f_2 with v in V_nt (unit vector), delta in C.
# For every column triple S: Pi_S = I_3 cap C^{3xS}; if ell != 0 on Pi_S then perm_3 = k ell^3 on Pi_S (ZBF).
# Objective = sum over S and pairs of test vectors of |P(v_i) ell(v_j)^3 - P(v_j) ell(v_i)^3|^2 ; multi-start least squares.
import sys, itertools, numpy as np; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
from scipy.optimize import least_squares
from pairlib import nullspace, rank, perm
import t8_two_minimal as T8
rng=np.random.default_rng(31)
def rnd(*k): return rng.normal(size=k)+1j*rng.normal(size=k)
def setup(s12,s13):
    w2,A1,A2=T8.struct(*s12); w3,B1,B3=T8.struct(*s13)
    y12=(-1+s12[2]*1j)/2; y13=(-1+s13[2]*1j)/2
    one=np.ones(5); z=np.zeros(5)
    def F(rows):
        v=np.zeros((3,5),complex)
        for i,vec in rows: v[i]=vec
        return v.reshape(-1)
    Fs=np.array([F([(0,one)]),F([(1,one)]),F([(2,one)]),F([(0,A1),(1,A2)]),F([(0,B1),(2,B3)])])
    A0=np.array([F([(0,one),(1,-one)]),F([(0,one),(2,-one)]),F([(0,A1+y12*one),(1,A2)]),F([(0,B1+y13*one),(2,B3)])])
    K=nullspace(Fs); M0=np.eye(15)[5:]@K; u=np.array([one,1/w2,1/w3]); cons=[]
    for S in itertools.combinations(range(5),3):
        Sc=[c for c in range(5) if c not in S]
        if rank(Fs[:,[i*5+c for i in range(3) for c in S]])<5: continue
        E=nullspace(K[[i*5+c for i in range(3) for c in Sc],:])
        if E.shape[1]!=4: continue
        def cfun(v,E=E,S=S):
            tau=(K@(E@v)).reshape(3,5); return perm((tau*u)[:,list(S)])
        facs=T8.linfactors(cfun)
        if facs is None: continue
        cons.append((M0@E,facs))
    R12=np.eye(15)[:10]@K; R13=np.vstack([np.eye(15)[:5],np.eye(15)[10:]])@K; r12=rank(R12); r13=rank(R13)
    sols=[]
    def dfs(idx,V):
        if V.shape[1]==0: return
        Nu=(M0.T@V).T
        if rank(np.vstack([R12,Nu]))==r12 or rank(np.vstack([R13,Nu]))==r13: return
        if idx==len(cons):
            if not any(rank(np.hstack([W,V]))==rank(W)==rank(V) for W in sols): sols.append(V)
            return
        R,facs=cons[idx]
        dfs(idx+1,V@nullspace(R.T@V))
        for lam in facs:
            Pk=np.linalg.svd(lam[None,:])[2][1:].conj().T
            if np.abs(lam@Pk).max()>1e-9: Pk=nullspace(lam[None,:])
            dfs(idx+1,V@nullspace(Pk.T@R.T@V))
    dfs(0,np.eye(10,dtype=complex))
    # keep maximal leaves only
    sols=[V for V in sols if not any(W is not V and rank(np.hstack([W,V]))==rank(W) and rank(W)>rank(V) for W in sols)]
    triv=np.array([np.concatenate([one,z]),np.concatenate([z,one]),np.concatenate([A2,-B3]) if np.abs(A1-B1).max()<1e-9 else np.concatenate([A2,B3])]).T
    return A0,u,sols,triv
def objective_factory(A0,u,V,triv):
    # V_nt: complement of triv inside V
    Q,_=np.linalg.qr(triv); Vp=V-Q@(Q.conj().T@V); uu,ss,vh=np.linalg.svd(Vp,full_matrices=False); r=int(np.sum(ss>1e-8)); Vnt=uu[:,:r]
    f2=np.concatenate([np.ones(5),np.zeros(5)]).astype(complex)
    tests={S:rnd(5,9) for S in itertools.combinations(range(5),3)}
    def resid(x):
        c=x[:2*r].view(complex) if False else (x[:r]+1j*x[r:2*r]); delta=x[2*r]+1j*x[2*r+1]
        nrm=np.sqrt(np.linalg.norm(c)**2+abs(delta)**2); c=c/nrm; delta=delta/nrm
        m=Vnt@c+delta*f2; n=np.concatenate([np.zeros(5),m])
        res=[]; nB1=0
        for S in itertools.combinations(range(5),3):
            cols=[i*5+j for i in range(3) for j in S]
            A=np.vstack([A0[:,cols],n[cols][None,:]])
            uS,sS,vhS=np.linalg.svd(A); rk=int(np.sum(sS>1e-9*max(1,sS[0]))); Nb=vhS[rk:].conj().T
            P=Nb@Nb.conj().T; vs=(P@tests[S].T).T
            ell=vs[:,:3].sum(axis=1); pm=np.array([perm((v.reshape(3,3)*u[:,list(S)])) for v in vs])
            if np.abs(ell).max()>1e-6: nB1+=1
            for i in range(5):
                for j in range(i+1,5): res.append(pm[i]*ell[j]**3-pm[j]*ell[i]**3)
        res=np.array(res); pen=1e3*max(0.0,abs(delta)-0.995)   # keep away from the spurious point n** = f_2 (ell = 0 on I_3)
        return np.concatenate([res.real,res.imag,[pen]]),nB1
    return resid,r
if __name__=='__main__':
    cfgs=[l for l in open('/home/kevxhk/work/L-gct-210/stage2/r3_survivors.txt').read().split('\n') if l.strip()] if False else None
    surv=[(('II',(0,1,2,2,2),1),('II',(0,1,2,2,2),-1)),(('II',(0,1,1,1,2),1),('II',(0,1,1,1,2),-1)),(('II',(0,0,0,1,2),1),('II',(0,0,0,1,2),-1)),
          (('II',(0,0,0,1,2),1),('II',(0,0,1,0,2),1)),(('II',(0,0,0,1,2),1),('II',(0,1,0,0,2),1)),(('II',(0,0,0,1,2),1),('II',(0,1,1,0,2),1)),
          (('II',(0,0,0,1,2),1),('II',(1,0,0,0,2),1)),(('II',(0,0,0,1,2),1),('II',(1,0,1,0,2),1)),(('II',(0,0,0,1,2),1),('II',(1,1,0,0,2),1)),
          (('II',(0,1,1,2,2),1),('II',(0,1,1,2,2),-1)),(('II',(0,0,1,2,2),1),('II',(0,0,1,2,2),-1)),(('II',(0,0,1,1,2),1),('II',(0,0,1,1,2),-1)),
          (('II',(0,0,1,1,2),1),('II',(0,1,0,0,2),1)),(('II',(0,0,1,1,2),1),('II',(1,0,0,0,2),1)),(('II',(0,0,1,1,2),1),('II',(1,1,0,0,2),1))]
    which=[int(a) for a in sys.argv[1:]] if len(sys.argv)>1 else range(len(surv))
    for idx in which:
        s12,s13=surv[idx]; A0,u,sols,triv=setup(s12,s13)
        best_all=[]
        for V in sols:
            resid,r=objective_factory(A0,u,V,triv); best=(1e9,None,None); rec=[]
            for trial in range(12):
                x0=rng.normal(size=2*r+2)
                sol=least_squares(lambda x: resid(x)[0],x0,method='lm',max_nfev=400)
                val=np.linalg.norm(resid(sol.x)[0]); nb=resid(sol.x)[1]
                xx=sol.x; cc=xx[:r]+1j*xx[r:2*r]; dd=xx[2*r]+1j*xx[2*r+1]; nn=np.sqrt(np.linalg.norm(cc)**2+abs(dd)**2)
                rec.append((val,nb,abs(dd)/nn))
                if val<best[0]: best=(val,sol.x,nb)
            good=sorted(set((nb,round(dl,3)) for (val,nb,dl) in rec if val<1e-8))
            best_all.append((V.shape[1],r,best[0],best[2],good))
        print(idx,s12[1:],s13[1:],' leaves:',len(sols),' (dim V, dim V_nt, min cube residual, #S with ell!=0 at min, list of (#S with ell!=0, |delta|) over zero-residual runs):',[(a,b,'%.2e'%c,d,g) for a,b,c,d,g in best_all],flush=True)
