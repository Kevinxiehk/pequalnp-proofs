# Round 3: inspect the admissible fifth annihilators n** = (0,m_2,m_3) for the surviving (II,II,lam=3) configurations
# (same necessary conditions as t8_two_minimal.py); print the distinct solution spaces of nu = n**|K modulo row-1 functionals,
# in the basis of "block-sum" functionals when possible.
import sys, itertools, numpy as np; sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
from pairlib import nullspace, rank, perm
import t8_two_minimal as T8
rng=np.random.default_rng(12)
def leaves(s12,s13):
    w2,A1,A2=T8.struct(*s12); w3,B1,B3=T8.struct(*s13)
    one=np.ones(5)
    def F(rows):
        v=np.zeros((3,5),complex)
        for i,vec in rows: v[i]=vec
        return v.reshape(-1)
    Fs=np.array([F([(0,one)]),F([(1,one)]),F([(2,one)]),F([(0,A1),(1,A2)]),F([(0,B1),(2,B3)])])
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
        cons.append((S,M0@E,facs))
    R1=np.eye(15)[:5]@K; r1=rank(R1); sols=[]
    def dfs(idx,V,path):
        if V.shape[1]==0 or rank(np.vstack([R1,(M0.T@V).T]))==r1: return
        if idx==len(cons): sols.append((V,path)); return
        S,R,facs=cons[idx]
        dfs(idx+1,V@nullspace(R.T@V),path+[0])
        for k,lam in enumerate(facs):
            Pk=np.linalg.svd(lam[None,:])[2][1:].conj().T
            if np.abs(lam@Pk).max()>1e-9: Pk=nullspace(lam[None,:])
            dfs(idx+1,V@nullspace(Pk.T@R.T@V),path+[k+1])
    dfs(0,np.eye(10,dtype=complex),[])
    # distinct nu-spaces modulo R1
    out=[]
    for V,path in sols:
        Nu=(M0.T@V).T                                  # rows: nu vectors
        key=np.vstack([R1,Nu]); 
        if not any(rank(np.vstack([k2,key]))==rank(k2)==rank(key) for k2 in out): out.append(key)
    return out,cons,K,M0,R1
if __name__=='__main__':
    cfgs=[(('II',(0,1,1,1,2),1),('II',(0,1,1,1,2),-1)),(('II',(0,1,1,1,2),1),('II',(1,0,0,0,2),1)),
          (('II',(0,1,1,2,2),1),('II',(0,1,1,2,2),-1)),(('II',(0,0,0,1,2),1),('II',(0,0,1,0,2),1))]
    for s12,s13 in cfgs:
        out,cons,K,M0,R1=leaves(s12,s13)
        print(s12[1:],s13[1:],' #constraints',len(cons),' distinct solution spaces mod row-1:',len(out),' dims:',[rank(k)-rank(R1) for k in out])
        # describe each space: which block-sum functionals of rows 2,3 lie in it?  test candidates sum_{cell} tau_2, sum_{cell} tau_3
        c12=np.array(s12[1]); c13=np.array(s13[1])
        cands={}
        for q in range(3):
            v=np.zeros((3,5)); v[1]=(c12==q); cands['row2:Q%d(12)'%(q+1)]=v.reshape(-1)@K
            v=np.zeros((3,5)); v[2]=(c13==q); cands['row3:Q%d(13)'%(q+1)]=v.reshape(-1)@K
            v=np.zeros((3,5)); v[1]=(c13==q); cands['row2:Q%d(13)'%(q+1)]=v.reshape(-1)@K
            v=np.zeros((3,5)); v[2]=(c12==q); cands['row3:Q%d(12)'%(q+1)]=v.reshape(-1)@K
        for j in range(5):
            v=np.zeros((3,5)); v[1,j]=1; cands['tau2(%d)'%j]=v.reshape(-1)@K
            v=np.zeros((3,5)); v[2,j]=1; cands['tau3(%d)'%j]=v.reshape(-1)@K
        for k in out[:6]:
            inside=[nm for nm,vec in cands.items() if rank(np.vstack([k,vec]))==rank(k)]
            print('    dim',rank(k)-rank(R1),' contains (mod row-1 functionals):',inside)
