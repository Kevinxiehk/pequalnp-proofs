# Round 2 sanity for the algebraic lemmas used in the GEN analysis (all are hand proofs; this only guards against slips).
import sys, itertools, numpy as np; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
from pairlib import perm, rank, nullspace
rng=np.random.default_rng(5)
def rnd(*k): return rng.normal(size=k)+1j*rng.normal(size=k)
# (a) quadratic / cubic monomials restricted to the hyperplane sum c = 0 are independent (3 and 4 variables)
def indep(nvar,deg):
    B=nullspace(np.ones((1,nvar)))          # basis of hyperplane
    mons=list(itertools.combinations(range(nvar),deg)); rows=[]
    for _ in range(60):
        c=B@rnd(nvar-1); rows.append([np.prod(c[list(m)]) for m in mons])
    return len(mons),rank(np.array(rows))
print('(a) squarefree monomials on {sum c=0}: (n,deg)->(#mons,rank):',{(n,d):indep(n,d) for (n,d) in [(3,2),(4,2),(4,3)]})
# (b) 3x3 lemma: equal row sums 1, pairwise row products 1, perm = 0  =>  two rows equal.  LM search from random starts.
def solve(nr,nc,trials=40):
    best=[]
    for t in range(trials):
        x=rnd(nr*nc)
        def F(x):
            G=x.reshape(nr,nc); r=[G[i].sum()-1 for i in range(nr)]
            r+=[G[i]@G[k]-1 for i in range(nr) for k in range(i+1,nr)]
            r+=[perm(G[list(I)][:,list(S)]) for I in itertools.combinations(range(nr),3) for S in itertools.combinations(range(nc),3)]
            return np.array(r)
        lam=1e-3
        for it in range(200):
            r=F(x); Jm=np.zeros((len(r),len(x)),complex); h=1e-7
            for k in range(len(x)):
                e=np.zeros(len(x),complex); e[k]=h; Jm[:,k]=(F(x+e)-r)/h
            dx=np.linalg.lstsq(Jm.conj().T@Jm+lam*np.eye(len(x)),-Jm.conj().T@r,rcond=None)[0]
            if np.linalg.norm(F(x+dx))<np.linalg.norm(r): x=x+dx; lam=max(lam/3,1e-12)
            else: lam*=5
            if np.linalg.norm(r)<1e-12: break
        G=x.reshape(nr,nc); res=np.linalg.norm(F(x))
        best.append((res,np.abs(G).min(),min(np.abs(G[i]-G[k]).max() for i in range(nr) for k in range(i+1,nr))))
    return best
b=solve(3,3,30); sol=[x for x in b if x[0]<1e-9]
print('(b) 3x3: %d of %d runs converged; among them min |entry| >= %.2e ; max over solutions of (min row-difference) = %.2e'%(len(sol),len(b),min(x[1] for x in sol),max(x[2] for x in sol)))
b=solve(4,3,30); sol=[x for x in b if x[0]<1e-9]
print('(c) 4x3 (all four 3x3 perms zero): converged runs:',len(sol),' of',len(b),'; smallest |entry| among converged:',['%.1e'%x[1] for x in sol][:8])
