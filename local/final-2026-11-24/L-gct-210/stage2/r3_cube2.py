# Round 3: full cube condition on the 12 configurations surviving r3_survey.py (fast version).
# For each admissible leaf V of fifth annihilators n** = (0,m): parameters m = v + delta*f_2 (v in V_nt, |v|^2+|delta|^2 = 1).
# Residuals: for every column triple S and pairs of test vectors of Pi_S: P(v_i) ell(v_j)^3 - P(v_j) ell(v_i)^3.
import sys, itertools, numpy as np; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
from scipy.optimize import least_squares
from pairlib import nullspace, rank
import r3_survey as RS
rng=np.random.default_rng(77)
def rnd(*k): return rng.normal(size=k)+1j*rng.normal(size=k)
def perm3(M):
    a,b,c=M[0]; d,e,f=M[1]; g,h,k=M[2]
    return a*(e*k+f*h)+b*(d*k+f*g)+c*(d*h+e*g)
def leaves(s12,s13):
    w2,A1,A2,y12=RS.typeII(*s12); w3,B1,B3,y13=RS.typeII(*s13); one=np.ones(5); z=np.zeros(5)
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
        E=Pt@nullspace(ell[None,:]); d=E.shape[1]
        def cfun(v,E=E,S=S): return perm3(((E@v).reshape(3,3))*u[:,list(S)])
        facs=RS.linfactors(cfun,d)
        if facs is None: continue
        R=np.zeros((10,d),complex)
        for k,j in enumerate(S): R[j]=E[3+k]; R[5+j]=E[6+k]
        cons.append((R,facs))
    def Bspace(vecs,which):
        Bm=np.zeros((10,7),complex); k=0
        for j in range(5): Bm[(0 if which==2 else 5)+j,k]=1; k+=1
        for v in vecs: Bm[(5 if which==2 else 0):(10 if which==2 else 5),k]=v; k+=1
        return Bm
    B12=Bspace([one,B3],2); B13=Bspace([one,A2],3); r12=rank(B12); r13=rank(B13); sols=[]
    def dfs(idx,V):
        if V.shape[1]==0 or rank(np.hstack([B12,V]))==r12 or rank(np.hstack([B13,V]))==r13: return
        if idx==len(cons):
            if not any(rank(np.hstack([W,V]))==rank(W) for W in sols): sols.append(V)
            return
        R,facs=cons[idx]
        dfs(idx+1,V@nullspace(R.T@V))
        for lam in facs:
            Pk=np.linalg.svd(lam[None,:])[2][1:].conj().T
            if np.abs(lam@Pk).max()>1e-9: Pk=nullspace(lam[None,:])
            dfs(idx+1,V@nullspace(Pk.T@R.T@V))
    dfs(0,np.eye(10,dtype=complex))
    sols=[V for V in sols if not any(W is not V and W.shape[1]>V.shape[1] and rank(np.hstack([W,V]))==rank(W) for W in sols)]
    triv=np.array([np.concatenate([one,z]),np.concatenate([z,one]),np.concatenate([A2,-B3]) if np.abs(A1-B1).max()<1e-9 else np.concatenate([A2,B3])]).T
    return A0,u,sols,triv
def cube_min(A0,u,V,triv,trials=6):
    Q,_=np.linalg.qr(triv); Vp=V-Q@(Q.conj().T@V); uu,ss,vh=np.linalg.svd(Vp,full_matrices=False); r=int(np.sum(ss>1e-8)); Vnt=uu[:,:r]
    f2=np.concatenate([np.ones(5),np.zeros(5)]).astype(complex)
    Ss=list(itertools.combinations(range(5),3)); tests={S:rnd(4,9) for S in Ss}; cols={S:[i*5+j for i in range(3) for j in S] for S in Ss}
    def resid(x,info=False):
        c=x[:r]+1j*x[r:2*r]; delta=x[2*r]+1j*x[2*r+1]; nrm=np.sqrt(np.linalg.norm(c)**2+abs(delta)**2); c=c/nrm; delta=delta/nrm
        n=np.concatenate([np.zeros(5),Vnt@c+delta*f2]); res=[]; nB1=0
        for S in Ss:
            A=np.vstack([A0[:,cols[S]],n[cols[S]][None,:]])
            uS,sS,vhS=np.linalg.svd(A); rk=int(np.sum(sS>1e-9*max(1,sS[0]))); Nb=vhS[rk:].conj().T
            vs=(Nb@(Nb.conj().T@tests[S].T)).T
            ell=vs[:,:3].sum(axis=1); pm=np.array([perm3(v.reshape(3,3)*u[:,list(S)]) for v in vs])
            if np.abs(ell).max()>1e-6: nB1+=1
            for i in range(4):
                for j in range(i+1,4): res.append(pm[i]*ell[j]**3-pm[j]*ell[i]**3)
        res=np.array(res); pen=1e3*max(0.0,abs(delta)-0.995)
        out=np.concatenate([res.real,res.imag,[pen]])
        return (out,nB1,abs(delta)) if info else out
    best=(1e9,0,0)
    for t in range(trials):
        sol=least_squares(resid,rng.normal(size=2*r+2),method='lm',max_nfev=150*(2*r+3))
        o,nb,dl=resid(sol.x,True); val=np.linalg.norm(o)
        if val<best[0]: best=(val,nb,dl)
    return r,best
if __name__=='__main__':
    surv=[(((0,1,2,2,2),1),((0,1,2,2,2),-1)),(((0,1,1,1,2),1),((0,1,1,1,2),-1)),(((0,0,0,1,2),1),((0,0,0,1,2),-1)),
          (((0,0,0,1,2),1),((0,1,1,0,2),1)),(((0,0,0,1,2),1),((1,0,1,0,2),1)),(((0,0,0,1,2),1),((1,1,0,0,2),1)),
          (((0,1,1,2,2),1),((0,1,1,2,2),-1)),(((0,0,1,2,2),1),((0,0,1,2,2),-1)),(((0,0,1,1,2),1),((0,0,1,1,2),-1)),
          (((0,0,1,1,2),1),((0,1,0,0,2),1)),(((0,0,1,1,2),1),((1,0,0,0,2),1)),(((0,0,1,1,2),1),((1,1,0,0,2),1))]
    which=[int(a) for a in sys.argv[1:]] if len(sys.argv)>1 else range(len(surv))
    for idx in which:
        s12,s13=surv[idx]; A0,u,sols,triv=leaves(s12,s13); out=[]
        for V in sols:
            r,best=cube_min(A0,u,V,triv); out.append((V.shape[1],r,'%.2e'%best[0],best[1],'%.3f'%best[2]))
        print(idx,s12,s13,' leaves (dim V, dim V_nt, min cube residual, #S with ell!=0, |delta|):',out,flush=True)
