# Sanity of the (T2) test on known level spaces: for every row r with a_r = 1 (4-dim projection), (T2) must be solvable with
# sum_k T_k = J' modulo L_r.  Also tested on the transposes (columns with b_c = 1).  Control: a random subspace of the same dimension.
import sys, itertools, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/chief'); import core
A=list(sys.argv); sys.argv=[A[0]]
exec(open('/home/kevxhk/work/L-gct-210/stage2/r6_T2.py').read().split("if __name__=='__main__':")[0])
def T2gen(B,rg,npts=30):
    d=len(B); eqs=[]
    for _ in range(npts):
        xi=np.tensordot(rg.normal(size=d)+1j*rg.normal(size=d),B,axes=1); D=DG(xi)
        for j in range(5):
            for k in range(j,5):
                row=np.zeros((5,4,5),complex); row[k]+=D[j]; row[j]+=D[k]; eqs.append(row.ravel())
    Am=np.array(eqs); u,s,vh=np.linalg.svd(Am,full_matrices=True); r=int((s>1e-9*max(s[0],1e-300)).sum()); ns=vh[r:].conj()
    S=np.array([t.reshape(5,20).sum(axis=0) for t in ns]).T if len(ns) else np.zeros((20,0),complex); M=np.concatenate([S,B.reshape(d,20).T],axis=1)
    c,_,_,_=np.linalg.lstsq(M,np.ones(20,dtype=complex),rcond=None); return len(ns),np.linalg.norm(M@c-np.ones(20))
def rank(M,tol=1e-8):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol).sum())
rg=np.random.default_rng(2)
for name,sp in core.SP.items():
    L=np.array([np.array(m,dtype=complex) for m in sp()]); d=len(L)
    for tr,Lt in (('rows',L),('cols',L.transpose(0,2,1))):
        for r in range(5):
            if rank(Lt[:,r,:])!=4: continue
            # L_r: elements with zero row r
            u,s,vh=np.linalg.svd(Lt[:,r,:]); coef=u[:,4:].conj().T            # combinations with zero row r
            Lr=np.tensordot(coef,Lt,axes=1); Lr=np.delete(Lr,r,axis=1)        # (d-4,4,5)
            # G = 0 on L_r ?
            xi=np.tensordot(rg.normal(size=len(Lr))+1j*rg.normal(size=len(Lr)),Lr,axes=1)
            g=max(abs(sum(np.prod([np.delete(xi,j,axis=1)[i,p[i]] for i in range(4)]) for p in itertools.permutations(range(4)))) for j in range(5))
            n,err=T2gen(Lr,rg); ctrl=T2gen(rg.normal(size=Lr.shape)+1j*rg.normal(size=Lr.shape),rg)[1]
            print('%-11s %s, line %d (full projection): dim L_r = %d, |G| on L_r = %.1e, (T2): distance of J\' = %.1e   [control, random space: %.1e]'%(name,tr,r,len(Lr),g,err,ctrl),flush=True)
